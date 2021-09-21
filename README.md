# Verifying a Multiprocessor Hypervisor on Arm Relaxed Memory Hardware

This artifact includes the mechanized Coq proofs for the security of SeKVM, our verified multiprocessor hypervisor, on Arm relaxed memory hardware. 
It also provides instructions on running the performance evaluations of SeKVM.

# Table of Contents
  - [1. Coq Proofs](#1-coq-proofs)
    - [1.1 Proofs of main theorems in the paper](#11-proofs-of-main-theorems-in-the-paper)
      - [1.1.1 Theorem 2 : when the kernel runs in isolation](#111-theorem-2--when-the-kernel-runs-in-isolation)
      - [1.1.2 Theorem 4 : when the kernel runs with user codes](#112-theorem-4--when-the-kernel-runs-with-user-codes)
    - [1.2 Proofs that SeKVM satisfies the wDRF conditions](#12-proofs-that-sekvm-satisfies-the-wdrf-conditions)
    - [1.3 Proofs of SeKVM on SC hardware](#13-proofs-of-sekvm-on-sc-hardware)
      - [1.3.1 34 Security-preserving layers](#131-34-security-preserving-layers)
      - [1.3.2 Bottom layer machine definition](#132-bottom-layer-machine-definition)
      - [1.3.3 Top-layer Security](#133-top-layer-security)
  - [2. Performance Evaluation](#2-performance-evaluation)
    - [2.1 Prerequisites](#21-prerequisites)
    - [2.2 Instructions for Cloudlab](#22-instructions-for-cloudlab)
      - [2.2.1 Joining Cloudlab](#221-joining-cloudlab)
      - [2.2.2 Cloudlab profiles](#222-cloudlab-profiles)
    - [2.3 Overview](#23-overview)
    - [2.4 Basic preparation](#24-basic-preparation)
      - [2.4.1 Clone the Artifact Repo](#241-clone-the-artifact-repo)
      - [2.4.2 Download the VM Image](#242-download-the-vm-image)
      - [2.4.3 Create Multiple VMs Images](#243-create-multiple-vms-images)
    - [2.5 QEMU Setup](#25-qemu-setup)
      - [2.5.1 QEMU compilation for KVM](#251-qemu-compilation-for-kvm)
      - [2.5.2 QEMU compilation for SeKVM](#252-qemu-compilation-for-sekvm)
    - [2.6 SeKVM Setup](#26-sekvm-setup)
      - [2.6.1 SeKVM Configuration & Compilation](#261-sekvm-configuration--compilation)
      - [2.6.2 SeKVM Installation](#262-sekvm-installation)
    - [2.7 Running a virtual machine](#27-running-a-virtual-machine)
    - [2.8 Terminating a virtual machine](#28-terminating-a-virtual-machine)
    - [2.9 Client Setup](#29-client-setup)
    - [2.10 Running Application Benchmarks and Collect Results](#210-running-application-benchmarks-and-collect-results)
      - [2.10.1 Apache/MongoDB/Redis](#2101-apachemongodbredis)
      - [2.10.2 Hackbench/Kernbench](#2102-hackbenchkernbench)
    - [2.11 Running Multi-VMs](#211-running-multi-vms)
      - [2.11.1 Launch VMs](#2111-launch-vms)
      - [2.11.2 Apache/MongoDB/Redis](#2112-apachemongodbredis)
      - [2.11.3 Hackbench/Kernbench](#2113-hackbenchkernbench)
      - [2.11.4 Shutdown VMs](#2114-shutdown-vms)
    - [2.12 Running Microbenchmarks](#212-running-microbenchmarks)

## 1. Coq Proofs

The Coq proofs of this work have three components. First, we prove the theorems in Section 4 of the paper. 
These theorems guarantee that if a system satisfies a set of synchronization and memory
access conditions that we call the wDRF conditions, then any observable behavior on the Arm relaxed memory hardware
is also observable on the sequential consistent (SC) hardware model. Second, we prove that SeKVM satisfies the wDRF conditions.
Third, we prove the security of SeKVM on the SC model. 
Together, these three components guarantee the security of SeKVM on Arm relaxed memory hardware.

### 1.1 Proofs of main theorems in the paper

Here we include the mechanized proofs of Theorem 2 and Theorem 4 in Section 4. Note that Theorem 1 and Theorem 3 are both weakened versions of Theorem 4. 
There correctness automatically hold after Theorem 4 is proved.

#### 1.1.1 Theorem 2 : when the kernel runs in isolation

| file | description |
| ---- | ---- |
| [Base_Isolated](proofs/theorem2/Base_Isolated.md) | Basic definitions |
| [SC_Isolated](proofs/theorem2/SC_Isolated.md) | The sequential consistent hardware model |
| [Promising_Isolated](proofs/theorem2/Promising_Isolated.md) | The Promising-Arm relaxed memory model |
| [DRF_Isolated](proofs/theorem2/DRF_Isolated.md) | DRF and no-barrier-misuse conditions |
| [Proof_Isolated](proofs/theorem2/Proof_Isolated.md) | Proof of the theorem |

#### 1.1.2 Theorem 4 : when the kernel runs with user codes
In the proof of Theorem 4, we use data oracles to model user behavior. Details can be seen from the following files.
| file | description |
| ---- | ---- |
| [Base_Full](proofs/theorem4/Base_Full.md) | Basic definitions (with user behavior) |
| [SC_Full](proofs/theorem4/SC_Full.md) | The sequential consistent hardware model (with user behavior) |
| [Promising_Full](proofs/theorem4/Promising_Full.md) | The Promising-Arm relaxed memory model (with user behavior) |
| [DRF_Full](proofs/theorem4/DRF_Full.md) | DRF and no-barrier-misuse conditions (with user behavior) |
| [PageTable_Full](proofs/theorem4/PageTable_Full.md) | Page table behavior model and proof (with user behavior) |
| [Proof_Full](proofs/theorem4/Proof_Full.md) | Proof of the theorem (with user behavior) |

### 1.2 Proofs that SeKVM satisfies the wDRF conditions

| condition | proof |
| -----  | ----- |
| DRF-Kernel | [DRF_and_Barrier](proofs/sekvm/wDRF/DRF_and_Barrier.md) |
| No-Barrier-Misuse | [DRF_and_Barrier](proofs/sekvm/wDRF/DRF_and_Barrier.md) |
| Weak-Memory-Isolation | [MemoryIsolation](proofs/sekvm/wDRF/MemoryIsolation.md) | 
| Transactional-Page-Table | [Transactional](proofs/sekvm/wDRF/Transactional.md) | 
| Write-Once-Kernel-Mapping| [WriteOnceKernelMapping](proofs/sekvm/wDRF/WriteOnceKernelMapping.md) | 


### 1.3 Proofs of SeKVM on SC hardware  

#### 1.3.1 34 Security-preserving layers

| #  | **Layer**               | **Specification**      | **Code Verification**       | **Source Code**        | **Refinement**           |
| -- | -----                   | -------------          | -----------------           | -----------            | ----------               |
|    | **Hypercall/Exception** |                        |                             |                        |                          |
| 34 | [TrapHandler][]         | [TrapHandlerSpec][]    | [TrapHandlerProofCode][]    | [TrapHandlerCode][]    | [TrapHandlerRefine][]    |
| 33 | [TrapHandlerRaw][]      | [TrapHandlerRawSpec][] | [TrapHandlerRawProofCode][] | [TrapHandlerRawCode][] | [TrapHandlerRawRefine][] |
| 32 | [TrapDispatcher][]      | [TrapDispatcherSpec][] | [TrapDispatcherProofCode][] | [TrapDispatcherCode][] | [TrapDispatcherRefine][] |
| 31 | [FaultHandler][]        | [FaultHandlerSpec][]   | [FaultHandlerProofCode][]   | [FaultHandlerCode][]   | [FaultHandlerRefine][]   |
| 30 | [MemHandler][]          | [MemHandlerSpec][]     | [MemHandlerProofCode][]     | [MemHandlerCode][]     | [MemHandlerRefine][]     |
|    | **VCPU Context**        |                        |                             |                        |                          |
| 29 | [CtxtSwitch][]          | [CtxtSwitchSpec][]     | [CtxtSwitchProofCode][]     | [CtxtSwitchCode][]     | [CtxtSwitchRefine][]     |
| 28 | [VCPUOps][]             | [VCPUOpsSpec][]        | [VCPUOpsProofCode][]        | [VCPUOpsCode][]        | [VCPUOpsRefine][]        |
| 27 | [VCPUOpsAux][]          | [VCPUOpsAuxSpec][]     | [VCPUOpsAuxProofCode][]     | [VCPUOpsAuxCode][]     | [VCPUOpsAuxRefine][]     |
|    | **SMMU**                |                        |                             |                        |                          |
| 26 | [MmioOps][]             | [MmioOpsSpec][]        | [MmioOpsProofCode][]        | [MmioOpsCode][]        | [MmioOpsRefine][]        |
| 25 | [MmioOpsAux][]          | [MmioOpsAuxSpec][]     | [MmioOpsAuxProofCode][]     | [MmioOpsAuxCode][]     | [MmioOpsAuxRefine][]     |
| 24 | [MmioCore][]            | [MmioCoreSpec][]       | [MmioCoreProofCode][]       | [MmioCoreCode][]       | [MmioCoreRefine][]       |
| 23 | [MmioCoreAux][]         | [MmioCoreAuxSpec][]    | [MmioCoreAuxProofCode][]    | [MmioCoreAuxCode][]    | [MmioCoreAuxRefine][]    |
| 22 | [MmioRaw][]             | [MmioRawSpec][]        | [MmioRawProofCode][]        | [MmioRawCode][]        | [MmioRawRefine][]        |
|    | **VMBoot/Management**   |                        |                             |                        |                          |
| 21 | [BootOps][]             | [BootOpsSpec][]        | [BootOpsProofCode][]        | [BootOpsCode][]        | [BootOpsRefine][]        |
| 20 | [BootAux][]             | [BootAuxSpec][]        | [BootAuxProofCode][]        | [BootAuxCode][]        | [BootAuxRefine][]        |
| 19 | [BootCore][]            | [BootCoreSpec][]       | [BootCoreProofCode][]       | [BootCoreCode][]       | [BootCoreRefine][]       |
| 18 | [VMPower][]             | [VMPowerSpec][]        | [VMPowerProofCode][]        | [VMPowerCode][]        | [VMPowerRefine][]        |
|    | **S2Page**              |                        |                             |                        |                          |
| 17 | [MemoryOps][]           | [MemoryOpsSpec][]      | [MemoryOpsProofCode][]      | [MemoryOpsCode][]      | [MemoryOpsRefine][]      |
| 16 | [MemManager][]          | [MemManagerSpec][]     | [MemManagerProofCode][]     | [MemManagerCode][]     | [MemManagerRefine][]     |
| 15 | [PageManager][]         | [PageManagerSpec][]    | [PageManagerProofCode][]    | [PageManagerCode][]    | [PageManagerRefine][]    |
| 14 | [PageIndex][]           | [PageIndexSpec][]      | [PageIndexProofCode][]      | [PageIndexCode][]      | [PageIndexRefine][]      |
| 13 | [MemRegion][]           | [MemRegionSpec][]      | [MemRegionProofCode][]      | [MemRegionCode][]      | [MemRegionRefine][]      |
|    | **SMMU Page Table**     |                        |                             |                        |                          |
| 12 | [MmioSPTOps][]          | [MmioSPTOpsSpec][]     | [MmioSPTOpsProofCode][]     | [MmioSPTOpsCode][]     | [MmioSPTOpsRefine][]     |
| 11 | [MmioSPTWalk][]         | [MmioSPTWalkSpec][]    | [MmioSPTWalkProofCode][]    | [MmioSPTWalkCode][]    | [MmioSPTWalkRefine][]    |
| 10 | [MmioPTWalk][]          | [MmioPTWalkSpec][]     | [MmioPTWalkProofCode][]     | [MmioPTWalkCode][]     | [MmioPTWalkRefine][]     |
| 9  | [MmioPTAlloc][]         | [MmioPTAllocSpec][]    | [MmioPTAllocProofCode][]    | [MmioPTAllocCode][]    | [MmioPTAllocRefine][]    |
|    | **Page Table**          |                        |                             |                        |                          |
| 8  | [NPTOps][]              | [NPTOpsSpec][]         | [NPTOpsProofCode][]         | [NPTOpsCode][]         | [NPTOpsRefine][]         |
| 7  | [NPTWalk][]             | [NPTWalkSpec][]        | [NPTWalkProofCode][]        | [NPTWalkCode][]        | [NPTWalkRefine][]        |
| 6  | [PTWalk][]              | [PTWalkSpec][]         | [PTWalkProofCode][]         | [PTWalkCode][]         | [PTWalkRefine][]         |
| 5  | [PTAlloc][]             | [PTAllocSpec][]        | [PTAllocProofCode][]        | [PTAllocCode][]        | [PTAllocRefine][]        |
|    | **Spinlock**            |                        |                             |                        |                          |
| 4  | [Locks][]               | [LocksSpec][]          | [LocksProofCode][]          | [LocksCode][]          | [LocksRefine][]          |
| 3  | [LockOpsH][]            | [LockOpsHSpec][]       | [LockOpsHProofCode][]       | [LockOpsHCode][]       | [LockOpsHRefine][]       |
| 2  | [LockOpsQ][]            | [LockOpsQSpec][]       | [LockOpsQProofCode][]       | [LockOpsQCode][]       | [LockOpsQRefine][]       |
| 1  | [LockOps][]             | [LockOpsSpec][]        | [LockOpsProofCode][]        | [LockOpsCode][]        | [LockOpsRefine][]        |
* Note: The `Source Code` column lists the Clight source code that we verified. Our verification is based on the C semantics (i.e., Clight) of CompCert, a certified C compiler. The Clight source code written in Coq are extracted from the output of CompCert's `clightgen` tool. To obtain the clight code, we slightly retrofit the original C source code before parsing them by `clightgen`, since KVM uses some features that are not supported by CompCert. For example, all function definitions of SeKVM have compilation flag `_hyp_text` that controls compiler to store all the code into a specific section of the binary, which is not supported by CompCert. After generating Coq code using `clightgen`, we also deleted unnecessary definitions from the generated output to make them computable using Coq 8.4 and unified the identifier definitions globally, i.e. we made each function have the same identifier in all generated Coq files. In the future, we can add these features into CompCert’s parser and Clight and link the C code and the proofs automatically.

#### 1.3.2 Bottom layer machine definition

These following definitions comprise the base layer of SeKVM's refinement proofs.
Note that AbstractMachineState defines the machine state,
and is used throughout the layer refinement proofs.

* Machine state definition: [AbstractMachineState][]

* Lock-related helpers: [AbstractMachineLocks][]

* Layer definition: [AbstractMachine][]

* Specification: [AbstractMachineSpec][]

#### 1.3.3 Top-layer Security

* Invariant definitions: [Invs][]

* Invariant proof: [InvProofs][]

* Security property definition: [SecurityDef][]

* Noninterference proof: [Noninterference][]


## 2. Performance Evaluation


We provide the instructions to run and test SeKVM as follows.

### 2.1 Prerequisites

* We leverage [Cloudlab.us](https://www.cloudlab.us/) which provides machines and preconfigured profiles. Machines will be available upon request for artifact evaluation. See [Instructions for Cloudlab](#22-instructions-for-cloudlab). For our profile, we include two physical Arm machines (server/client) connected by <em>private</em> network.
  
### 2.2 Instructions for Cloudlab

#### 2.2.1 Joining Cloudlab
Please sign up in cloud.us: https://www.cloudlab.us/signup.php to be able to access machines. Join the existing project: VirtualCloudTech, and we will receive a notification automatically and we will let you in.
To ensure anonymity, please use "SOSP21 AE #nonce" for full name, a one-time email address and random information in other fields.
#### 2.2.2 Cloudlab profiles
Use the `e6998-vct-m400` profile for running experiments. In **Cluster**, please select **Cloudlab Utah**. Please be patient and wait for the machines to setup and boot.

Once your machines are ready, you can login either via ssh or the UI interface. You have root access without password. You need to switch to root by:
```
# sudo su
```

### 2.3 Overview
On both the server and client machines, you need to do the [basic preparation](#24-basic-preparation) for running various scripts and compiling source code.

On both machines, Linux v4.18 is pre-installed, which includes KVM. You will need to first install [QEMU](#25-qemu-setup) to run the [VM](#27-running-a-virtual-machine). If you want to install SeKVM, you first need to use [a proper QEMU version](#25-qemu-setup), and then update the Linux on the server that includes the [SeKVM](#26-sekvm-setup). Once the installation is complete, you can start [running a virtual machine](#27-running-a-virtual-machine).

On the client, you have the v4.18 kerenl installed. Once the server is running a virtual machine (or none for bare-metal measurements), [run application benchmarks and collect results](#210-running-application-benchmarks-and-collect-results). The script to run the application benchmarks will output performance results.

### 2.4 Basic preparation

Clone this repository on both machines as a **root** user in the `\root` directory. Note that all the commands other than this `git clone` command need to be executed in the directory this repo is cloned.

```
# sudo su;
```

#### 2.4.1 Clone the Artifact Repo
On the server, you will need to clone the repo to a dedicated SSD mounted to `/mydata`.
```
# cd /mydata
# git clone https://github.com/VeriGu/sosp-paper211-ae.git
# cd sosp-paper211-ae 
```
On the client, you can just clone it to the home directory.
```
# cd /root
# git clone https://github.com/VeriGu/sosp-paper211-ae.git
# cd sosp-paper211-ae 
```

#### 2.4.2 Download the VM Image

We prepare different virtual disk images for different application workloads.

Benchmarks    | Image
--------------|:-----
Apache        | cloud-apache.img
Hackbench     | cloud-hack.img 
Kernbench     | cloud-kern.img
MongoDB       | cloud-mongo.img
Redis         | cloud-redis.img


To download the images, on the server, run
```
cd scripts/tools/
./download-images.sh
```
Images will be downloaded under `/mydata`.

#### 2.4.3 Create Multiple VMs Images

To run multiple VMs configuration, you will need to create an image for each VM for each benchmark:
```
# cd /mydata/sosp-paper211-ae/scripts/tools
# ./copy-image.sh
```

This may take around 10 minutes. You should see images been created under `/mydata`. For example, images for apache is named as `cloud-hack-i.img`.

The next sections explain how to compile and install QEMU and Linux kernel.

### 2.5 QEMU Setup

#### 2.5.1 QEMU compilation for KVM

You will be able to run KVM on the server after the compilation is finished. See here for [instructions to run VMs on KVM](#27-running-a-virtual-machine). Note that KVM can only run before SeKVM is installed.
```
# cd /srv/vm/qemu
# ./configure --target-list=aarch64-softmmu --disable-werror
# make -j8
```

To run SeKVM, you will first have to compile QEMU from the source code we modified to support SeKVM.

#### 2.5.2 QEMU compilation for SeKVM

Download QEMU source from the repo below and setup environment.
```
# cd /mydata/sosp-paper211-ae/
# git submodule update --init qemu
```
Wait for a moment for the clone to complete, then do the following.

```
# cd qemu
# ./configure --target-list=aarch64-softmmu --disable-werror
# make -j8
```

### 2.6 SeKVM Setup

The setup involves compiling and installing Linux/KVM on the server machine that includes SeKVM and **rebooting** the machine.

First, sync from remote to fetch the kernel source
```
# cd /mydata/sosp-paper211-ae/
# git submodule update --init linux
```

Please wait for a few minutes for the clone to complete. You will then see the source code in the linux/ directory.

#### 2.6.1 SeKVM Configuration & Compilation

```
# cd linux
# make sekvm_defconfig
# make -j8
# make modules_install
# make install
```

#### 2.6.2 SeKVM Installation

First switch to the directory of "sosp-paper211-ae". The following will install the newly compiled SeKVM binary to your boot partition, so u-boot can load and boot SeKVM on the hardware.
```
# cd /mydata/sosp-paper211-ae/scripts/tools/
# ./install-kernel.sh
# reboot
```

Each time after reboot, run `sudo su`.

### 2.7 Running a virtual machine 

To run virtual machines, please go to the directory sosp-paper211-ae/scripts.
```
# cd /mydata/sosp-paper211-ae/scripts/tests/
```

Run net.sh to create a virtual bridge to a network interface connecting the client machine. You only need to run it **once** whenever you (re)boot the host machine. You do not need to run it everytime you boot the VM.
```
# ../tools/net.sh
```

You can run the VM on SeKVM using the following command. `root/root` is the id/pwd needed for login.
Note that you can only run the benchmark correpsonding to image used by the VM.

```
# ./run-guest-sekvm.sh -i /mydata/cloud-apache.img
```
You can replace `run-guest-sekvm.sh` with `run-guest-kvm.sh` to run the VM in KVM, if SeKVM has not been installed and booted. You can replace `apache` with `hack`, `kern`, `mongo` or `redis` to run their corresponding benchmark.

### 2.8 Terminating a virtual machine

After the experiment, you need to terminate a virtual machine. Run `halt -p` command iteratively inside virtual machines  running **on the server** until you get the server shell.
```
[VM ~] # halt -p
```

### 2.9 Client Setup

The experiments measure various application performance on one machine, the server machine (i.e. bare-metal machine and virtual machines), while the other machine, which is the client machine, sends workloads to the server machine over the network.

Run this command **on the client machine**. It will automatically install all the applications for the performance evaluation on the server and the client machines.

**Note: all scripts under scripts/client should only be run on the client machine.**

When the client is ready, run the following to install the environment:

```
# cd /root/sosp-paper211-ae/scripts/client
# ./install.sh
```

### 2.10 Running Application Benchmarks and Collect Results

After all required packages are install on the client, you can then run the benchmark from the client machine using the respective script.

#### 2.10.1 Apache/MongoDB/Redis

For instance, to run apache/MongoDB/Redis, do the following:

```
# cd /root/sosp-paper211-ae/scripts/client
# ./prep-apache.sh 10.10.1.100
# ./apache.sh 10.10.1.100
```

You can replace `apache` with `mongo` or `redis` to run mongodb or redis.

The results will be stored at `scripts/client/apache.txt`.

#### 2.10.2 Hackbench/Kernbench

To run `hackbench`:
```
# cd /root/sosp-paper211-ae/scripts/client
# ./hack.sh 10.10.1.100
```

After hackbench is done, you can download the result from the server:
```
# ./grab-hack.sh 10.10.1.100
```
The result will be stored at `scripts/client/hackbench.txt`.

You can replace `hack` with `kern` to run kernbench.


### 2.11 Running Multi-VMs

We provide scripts for multiple VMs setup. Before you run benchmarks, make sure images for VMs and benchmark are [craeted](#243-create-multiple-vms-images).

We provide scripts to run multiple VMs benchmarks on the client. Due to hardware constraints, here we use 8 VMs.

#### 2.11.1 Launch VMs

You can launch VMs by:

```
# cd /mydata/sosp-paper211-ae/scripts/multi
# ./multi-sekvm.py apache
```
This script does not signal when it terminates. You should press Enter when there is no more output in the console. Same with multi-run.sh below.

Note that you can only run benchmarks correpsonding to image used by the VM. Due to IP address configuration, you cannot boot VMs for different benchmarks at the same time.
To run different benchmarks, you should first [shutdown](#2114-shutdown-vms) current VMs.

There are 56 available VMIDs in SeKVM. When they are exhausted, you will see an error "ioctl(KVM_CREATE_VM) failed: 22 Invalid argument    qemu-system-aarch64: failed to initialize KVM: Invalid argument    qemu-system-aarch64: kvm_init_vcpu failed: Input/output error". Then you need to reboot the server and relaunch VMs.


**Note: all scripts below under scripts/client should only be run on the client machine.**

To test the connection to the VM, run:

```
# ./multi-connection.sh
```
If some connection fails, reboot the server and relaunch VMs.

#### 2.11.2 Apache/MongoDB/Redis

You can run these benchmarks by:
```
# ./multi-prep.sh apache
# ./multi-run.sh apache
```

You can replace `apache` with `mongo` or `redis` to run mongodb or redis. `mongo` may trigger some intermediate errors which you can safely ignore.

The throughput numbers (ops/sec) of each VM/run will be appended at `scripts/client/apache.txt`.

#### 2.11.3 Hackbench/Kernbench

To run `hackbench`:
```
# ./multi-run.sh hack
```

After hackbench is done, you can download the result from the server:
```
# ./multi-grab.sh hack
```

The runtime numbers (sec) of each VM/run will be appended at `scripts/client/hackbench.txt`.


You can replace `hack` with `kern` to run kernbench. These two benchmarks take longer to run. For `hack`, wait for at least one minute before you determine there is no more output and then press Enter. For `kern`, wait for 5 minutes.

#### 2.11.4 Shutdown VMs

To shutdown VMs from the client, run:
```
# cd /root/sosp-paper211-ae/scripts/client
# ./multi-shutdown.sh
```
We use kvm-unit-test for microbenchmarks. kvm-unit-test creates a new VM for each measurement (please see arm-run in the source folder after untar). You can get the source of the benchmarks from here:
#### wget http://hp03.ncl.cs.columbia.edu/files/kvm-unit-test.tar.gz

### 2.12 Running Microbenchmarks
We measure the workloads using Arm’s cycle counters. By default, KVM does not allow VMs to access the counters. Thus, we would have to patch KVM to enable VM access. You can the patch for KVM from here:
#### wget http://hp03.ncl.cs.columbia.edu/files/kvm-micro-patch.diff
And the patch for SeKVM from here:
#### wget http://hp03.ncl.cs.columbia.edu/files/sekvm-micro-patch.diff

Before running the tests, you will have to recompile and reinstall KVM/SeKVM. For KVM, you should first **cd sosp-paper211-ae/linux** and do **git checkout HEAD~1** to checkout to the mainline Linux 4.18. For SeKVM you do not have to git checkout.

You can compile the source by **make -j8 && make modules_install && make install**, and install the new binaries by **cd /mydata/sosp-paper211-ae/scripts/tools/; ./install-kernel.sh**.

You also need to install perf in your system for testing microbenchmarks. You can compile perf by:
#### cd /mydata/sosp-paper211-ae/linux/tools/perf; make; cp perf /usr/bin/

Then download the 3 QMP scripts that we created to pin vCPUs to physical CPUs: isolate_vcpus.sh, pin_vcpus.sh, qmp-cpus. You can download them by replacing **$FILENAME** in the following command:
#### wget http://hp03.ncl.cs.columbia.edu/files/$FILENAME”.

Then, copy the above three scripts to
**QEMU for SeKVM:** /mydata/sosp-paper211-ae/qemu/scripts/qmp/
**QEMU for KVM:** /srv/vm/qemu/scripts/qmp

Then you can untar kvm-unit-test first, and compile the source by:
**./configure** and **make**.

You can now run the tests by running the respective script for KVM and SeKVM in kvm-uni-test/:
#### KVM: ./perf-kvm.sh
#### SeKVM: ./perf-sekvm.sh

You need to open a different terminal, ssh to the cloudlab server running KVM/SeKVM, then cd into the corresponding qemu/scripts/qmp and run **./isolate_cpu.sh**. The raw data will be written to the file **result** (Note that the old results will be removed). You can also use **./get-results.sh** to pull the numbers from **result**.

[AbstractMachineState]: proofs/sekvm/sekvm_layers/RData.md
[AbstractMachineLocks]: proofs/sekvm/sekvm_layers/CalLock.md
[AbstractMachine]: proofs/sekvm/sekvm_layers/AbstractMachine.md
[AbstractMachineSpec]: proofs/sekvm/sekvm_layers/AbstractMachineSpec.md

[LockOps]: proofs/sekvm/sekvm_layers/LockOps.md
[LockOpsSpec]: proofs/sekvm/sekvm_layers/LockOpsSpec.md
[LockOpsProofCode]: proofs/sekvm/sekvm_layers/LockOpsProofCode.md
[LockOpsCode]: proofs/sekvm/sekvm_layers/LockOpsCode.md
[LockOpsRefine]: proofs/sekvm/sekvm_layers/LockOpsRefine.md
[LockOpsQ]: proofs/sekvm/sekvm_layers/LockOpsQ.md
[LockOpsQSpec]: proofs/sekvm/sekvm_layers/LockOpsQSpec.md
[LockOpsQProofCode]: proofs/sekvm/sekvm_layers/LockOpsQProofCode.md
[LockOpsQCode]: proofs/sekvm/sekvm_layers/LockOpsQCode.md
[LockOpsQRefine]: proofs/sekvm/sekvm_layers/LockOpsQRefine.md
[LockOpsH]: proofs/sekvm/sekvm_layers/LockOpsH.md
[LockOpsHSpec]: proofs/sekvm/sekvm_layers/LockOpsHSpec.md
[LockOpsHProofCode]: proofs/sekvm/sekvm_layers/LockOpsHProofCode.md
[LockOpsHCode]: proofs/sekvm/sekvm_layers/LockOpsHCode.md
[LockOpsHRefine]: proofs/sekvm/sekvm_layers/LockOpsHRefine.md
[Locks]: proofs/sekvm/sekvm_layers/Locks.md
[LocksSpec]: proofs/sekvm/sekvm_layers/LocksSpec.md
[LocksProofCode]: proofs/sekvm/sekvm_layers/LocksProofCode.md
[LocksCode]: proofs/sekvm/sekvm_layers/LocksCode.md
[LocksRefine]: proofs/sekvm/sekvm_layers/LocksRefine.md
[PTAlloc]: proofs/sekvm/sekvm_layers/PTAlloc.md
[PTAllocSpec]: proofs/sekvm/sekvm_layers/PTAllocSpec.md
[PTAllocProofCode]: proofs/sekvm/sekvm_layers/PTAllocProofCode.md
[PTAllocCode]: proofs/sekvm/sekvm_layers/PTAllocCode.md
[PTAllocRefine]: proofs/sekvm/sekvm_layers/PTAllocRefine.md
[PTWalk]: proofs/sekvm/sekvm_layers/PTWalk.md
[PTWalkSpec]: proofs/sekvm/sekvm_layers/PTWalkSpec.md
[PTWalkProofCode]: proofs/sekvm/sekvm_layers/PTWalkProofCode.md
[PTWalkCode]: proofs/sekvm/sekvm_layers/PTWalkCode.md
[PTWalkRefine]: proofs/sekvm/sekvm_layers/PTWalkRefine.md
[NPTWalk]: proofs/sekvm/sekvm_layers/NPTWalk.md
[NPTWalkSpec]: proofs/sekvm/sekvm_layers/NPTWalkSpec.md
[NPTWalkProofCode]: proofs/sekvm/sekvm_layers/NPTWalkProofCode.md
[NPTWalkCode]: proofs/sekvm/sekvm_layers/NPTWalkCode.md
[NPTWalkRefine]: proofs/sekvm/sekvm_layers/NPTWalkRefine.md
[NPTOps]: proofs/sekvm/sekvm_layers/NPTOps.md
[NPTOpsSpec]: proofs/sekvm/sekvm_layers/NPTOpsSpec.md
[NPTOpsProofCode]: proofs/sekvm/sekvm_layers/NPTOpsProofCode.md
[NPTOpsCode]: proofs/sekvm/sekvm_layers/NPTOpsCode.md
[NPTOpsRefine]: proofs/sekvm/sekvm_layers/NPTOpsRefine.md
[MemRegion]: proofs/sekvm/sekvm_layers/MemRegion.md
[MemRegionSpec]: proofs/sekvm/sekvm_layers/MemRegionSpec.md
[MemRegionProofCode]: proofs/sekvm/sekvm_layers/MemRegionProofCode.md
[MemRegionCode]: proofs/sekvm/sekvm_layers/MemRegionCode.md
[MemRegionRefine]: proofs/sekvm/sekvm_layers/MemRegionRefine.md
[PageIndex]: proofs/sekvm/sekvm_layers/PageIndex.md
[PageIndexSpec]: proofs/sekvm/sekvm_layers/PageIndexSpec.md
[PageIndexProofCode]: proofs/sekvm/sekvm_layers/PageIndexProofCode.md
[PageIndexCode]: proofs/sekvm/sekvm_layers/PageIndexCode.md
[PageIndexRefine]: proofs/sekvm/sekvm_layers/PageIndexRefine.md
[PageManager]: proofs/sekvm/sekvm_layers/PageManager.md
[PageManagerSpec]: proofs/sekvm/sekvm_layers/PageManagerSpec.md
[PageManagerProofCode]: proofs/sekvm/sekvm_layers/PageManagerProofCode.md
[PageManagerCode]: proofs/sekvm/sekvm_layers/PageManagerCode.md
[PageManagerRefine]: proofs/sekvm/sekvm_layers/PageManagerRefine.md
[MemManager]: proofs/sekvm/sekvm_layers/MemManager.md
[MemManagerSpec]: proofs/sekvm/sekvm_layers/MemManagerSpec.md
[MemManagerProofCode]: proofs/sekvm/sekvm_layers/MemManagerProofCode.md
[MemManagerCode]: proofs/sekvm/sekvm_layers/MemManagerCode.md
[MemManagerRefine]: proofs/sekvm/sekvm_layers/MemManagerRefine.md
[MemoryOps]: proofs/sekvm/sekvm_layers/MemoryOps.md
[MemoryOpsSpec]: proofs/sekvm/sekvm_layers/MemoryOpsSpec.md
[MemoryOpsProofCode]: proofs/sekvm/sekvm_layers/MemoryOpsProofCode.md
[MemoryOpsCode]: proofs/sekvm/sekvm_layers/MemoryOpsCode.md
[MemoryOpsRefine]: proofs/sekvm/sekvm_layers/MemoryOpsRefine.md
[VMPower]: proofs/sekvm/sekvm_layers/VMPower.md
[VMPowerSpec]: proofs/sekvm/sekvm_layers/VMPowerSpec.md
[VMPowerProofCode]: proofs/sekvm/sekvm_layers/VMPowerProofCode.md
[VMPowerCode]: proofs/sekvm/sekvm_layers/VMPowerCode.md
[VMPowerRefine]: proofs/sekvm/sekvm_layers/VMPowerRefine.md
[BootCore]: proofs/sekvm/sekvm_layers/BootCore.md
[BootCoreSpec]: proofs/sekvm/sekvm_layers/BootCoreSpec.md
[BootCoreProofCode]: proofs/sekvm/sekvm_layers/BootCoreProofCode.md
[BootCoreCode]: proofs/sekvm/sekvm_layers/BootCoreCode.md
[BootCoreRefine]: proofs/sekvm/sekvm_layers/BootCoreRefine.md
[BootAux]: proofs/sekvm/sekvm_layers/BootAux.md
[BootAuxSpec]: proofs/sekvm/sekvm_layers/BootAuxSpec.md
[BootAuxProofCode]: proofs/sekvm/sekvm_layers/BootAuxProofCode.md
[BootAuxCode]: proofs/sekvm/sekvm_layers/BootAuxCode.md
[BootAuxRefine]: proofs/sekvm/sekvm_layers/BootAuxRefine.md
[BootOps]: proofs/sekvm/sekvm_layers/BootOps.md
[BootOpsSpec]: proofs/sekvm/sekvm_layers/BootOpsSpec.md
[BootOpsProofCode]: proofs/sekvm/sekvm_layers/BootOpsProofCode.md
[BootOpsCode]: proofs/sekvm/sekvm_layers/BootOpsCode.md
[BootOpsRefine]: proofs/sekvm/sekvm_layers/BootOpsRefine.md
[MmioPTAlloc]: proofs/sekvm/sekvm_layers/MmioPTAlloc.md
[MmioPTAllocSpec]: proofs/sekvm/sekvm_layers/MmioPTAllocSpec.md
[MmioPTAllocProofCode]: proofs/sekvm/sekvm_layers/MmioPTAllocProofCode.md
[MmioPTAllocCode]: proofs/sekvm/sekvm_layers/MmioPTAllocCode.md
[MmioPTAllocRefine]: proofs/sekvm/sekvm_layers/MmioPTAllocRefine.md
[MmioPTWalk]: proofs/sekvm/sekvm_layers/MmioPTWalk.md
[MmioPTWalkSpec]: proofs/sekvm/sekvm_layers/MmioPTWalkSpec.md
[MmioPTWalkProofCode]: proofs/sekvm/sekvm_layers/MmioPTWalkProofCode.md
[MmioPTWalkCode]: proofs/sekvm/sekvm_layers/MmioPTWalkCode.md
[MmioPTWalkRefine]: proofs/sekvm/sekvm_layers/MmioPTWalkRefine.md
[MmioSPTWalk]: proofs/sekvm/sekvm_layers/MmioSPTWalk.md
[MmioSPTWalkSpec]: proofs/sekvm/sekvm_layers/MmioSPTWalkSpec.md
[MmioSPTWalkProofCode]: proofs/sekvm/sekvm_layers/MmioSPTWalkProofCode.md
[MmioSPTWalkCode]: proofs/sekvm/sekvm_layers/MmioSPTWalkCode.md
[MmioSPTWalkRefine]: proofs/sekvm/sekvm_layers/MmioSPTWalkRefine.md
[MmioSPTOps]: proofs/sekvm/sekvm_layers/MmioSPTOps.md
[MmioSPTOpsSpec]: proofs/sekvm/sekvm_layers/MmioSPTOpsSpec.md
[MmioSPTOpsProofCode]: proofs/sekvm/sekvm_layers/MmioSPTOpsProofCode.md
[MmioSPTOpsCode]: proofs/sekvm/sekvm_layers/MmioSPTOpsCode.md
[MmioSPTOpsRefine]: proofs/sekvm/sekvm_layers/MmioSPTOpsRefine.md
[MmioRaw]: proofs/sekvm/sekvm_layers/MmioRaw.md
[MmioRawSpec]: proofs/sekvm/sekvm_layers/MmioRawSpec.md
[MmioRawProofCode]: proofs/sekvm/sekvm_layers/MmioRawProofCode.md
[MmioRawCode]: proofs/sekvm/sekvm_layers/MmioRawCode.md
[MmioRawRefine]: proofs/sekvm/sekvm_layers/MmioRawRefine.md
[MmioCoreAux]: proofs/sekvm/sekvm_layers/MmioCoreAux.md
[MmioCoreAuxSpec]: proofs/sekvm/sekvm_layers/MmioCoreAuxSpec.md
[MmioCoreAuxProofCode]: proofs/sekvm/sekvm_layers/MmioCoreAuxProofCode.md
[MmioCoreAuxCode]: proofs/sekvm/sekvm_layers/MmioCoreAuxCode.md
[MmioCoreAuxRefine]: proofs/sekvm/sekvm_layers/MmioCoreAuxRefine.md
[MmioCore]: proofs/sekvm/sekvm_layers/MmioCore.md
[MmioCoreSpec]: proofs/sekvm/sekvm_layers/MmioCoreSpec.md
[MmioCoreProofCode]: proofs/sekvm/sekvm_layers/MmioCoreProofCode.md
[MmioCoreCode]: proofs/sekvm/sekvm_layers/MmioCoreCode.md
[MmioCoreRefine]: proofs/sekvm/sekvm_layers/MmioCoreRefine.md
[MmioOpsAux]: proofs/sekvm/sekvm_layers/MmioOpsAux.md
[MmioOpsAuxSpec]: proofs/sekvm/sekvm_layers/MmioOpsAuxSpec.md
[MmioOpsAuxProofCode]: proofs/sekvm/sekvm_layers/MmioOpsAuxProofCode.md
[MmioOpsAuxCode]: proofs/sekvm/sekvm_layers/MmioOpsAuxCode.md
[MmioOpsAuxRefine]: proofs/sekvm/sekvm_layers/MmioOpsAuxRefine.md
[MmioOps]: proofs/sekvm/sekvm_layers/MmioOps.md
[MmioOpsSpec]: proofs/sekvm/sekvm_layers/MmioOpsSpec.md
[MmioOpsProofCode]: proofs/sekvm/sekvm_layers/MmioOpsProofCode.md
[MmioOpsCode]: proofs/sekvm/sekvm_layers/MmioOpsCode.md
[MmioOpsRefine]: proofs/sekvm/sekvm_layers/MmioOpsRefine.md
[VCPUOpsAux]: proofs/sekvm/sekvm_layers/VCPUOpsAux.md
[VCPUOpsAuxSpec]: proofs/sekvm/sekvm_layers/VCPUOpsAuxSpec.md
[VCPUOpsAuxProofCode]: proofs/sekvm/sekvm_layers/VCPUOpsAuxProofCode.md
[VCPUOpsAuxCode]: proofs/sekvm/sekvm_layers/VCPUOpsAuxCode.md
[VCPUOpsAuxRefine]: proofs/sekvm/sekvm_layers/VCPUOpsAuxRefine.md
[VCPUOps]: proofs/sekvm/sekvm_layers/VCPUOps.md
[VCPUOpsSpec]: proofs/sekvm/sekvm_layers/VCPUOpsSpec.md
[VCPUOpsProofCode]: proofs/sekvm/sekvm_layers/VCPUOpsProofCode.md
[VCPUOpsCode]: proofs/sekvm/sekvm_layers/VCPUOpsCode.md
[VCPUOpsRefine]: proofs/sekvm/sekvm_layers/VCPUOpsRefine.md
[CtxtSwitch]: proofs/sekvm/sekvm_layers/CtxtSwitch.md
[CtxtSwitchSpec]: proofs/sekvm/sekvm_layers/CtxtSwitchSpec.md
[CtxtSwitchProofCode]: proofs/sekvm/sekvm_layers/CtxtSwitchProofCode.md
[CtxtSwitchCode]: proofs/sekvm/sekvm_layers/CtxtSwitchCode.md
[CtxtSwitchRefine]: proofs/sekvm/sekvm_layers/CtxtSwitchRefine.md
[MemHandler]: proofs/sekvm/sekvm_layers/MemHandler.md
[MemHandlerSpec]: proofs/sekvm/sekvm_layers/MemHandlerSpec.md
[MemHandlerProofCode]: proofs/sekvm/sekvm_layers/MemHandlerProofCode.md
[MemHandlerCode]: proofs/sekvm/sekvm_layers/MemHandlerCode.md
[MemHandlerRefine]: proofs/sekvm/sekvm_layers/MemHandlerRefine.md
[FaultHandler]: proofs/sekvm/sekvm_layers/FaultHandler.md
[FaultHandlerSpec]: proofs/sekvm/sekvm_layers/FaultHandlerSpec.md
[FaultHandlerProofCode]: proofs/sekvm/sekvm_layers/FaultHandlerProofCode.md
[FaultHandlerCode]: proofs/sekvm/sekvm_layers/FaultHandlerCode.md
[FaultHandlerRefine]: proofs/sekvm/sekvm_layers/FaultHandlerRefine.md
[TrapDispatcher]: proofs/sekvm/sekvm_layers/TrapDispatcher.md
[TrapDispatcherSpec]: proofs/sekvm/sekvm_layers/TrapDispatcherSpec.md
[TrapDispatcherProofCode]: proofs/sekvm/sekvm_layers/TrapDispatcherProofCode.md
[TrapDispatcherCode]: proofs/sekvm/sekvm_layers/TrapDispatcherCode.md
[TrapDispatcherRefine]: proofs/sekvm/sekvm_layers/TrapDispatcherRefine.md
[TrapHandlerRaw]: proofs/sekvm/sekvm_layers/TrapHandlerRaw.md
[TrapHandlerRawSpec]: proofs/sekvm/sekvm_layers/TrapHandlerRawSpec.md
[TrapHandlerRawProofCode]: proofs/sekvm/sekvm_layers/TrapHandlerRawProofCode.md
[TrapHandlerRawCode]: proofs/sekvm/sekvm_layers/TrapHandlerRawCode.md
[TrapHandlerRawRefine]: proofs/sekvm/sekvm_layers/TrapHandlerRawRefine.md
[TrapHandler]: proofs/sekvm/sekvm_layers/TrapHandler.md
[TrapHandlerSpec]: proofs/sekvm/sekvm_layers/TrapHandlerSpec.md
[TrapHandlerProofCode]: proofs/sekvm/sekvm_layers/TrapHandlerProofCode.md
[TrapHandlerCode]: proofs/sekvm/sekvm_layers/TrapHandlerCode.md
[TrapHandlerRefine]: proofs/sekvm/sekvm_layers/TrapHandlerRefine.md
[Invs]: proofs/sekvm/sekvm_layers/SecurityInvs.md
[InvProofs]: proofs/sekvm/sekvm_layers/SecurityInvProofs.md
[SecurityDef]: proofs/sekvm/sekvm_layers/SecuritySecurityDef.md
[Noninterference]: proofs/sekvm/sekvm_layers/SecurityNoninterference.md
