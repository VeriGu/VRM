# Install SeKVM
Installing SeKVM is similar to installing vanilla KVM on Arm. Since KVM/ARM cannot be installed as a dedicated kernel module, you have to compile the entire kernel to install it. This document describes how to install SeKVM on a Cloudlab m400 Arm server.

## Configure Cloudlab profile to enable mass local storage
By default, m400 on cloudlab only provides 16GB disk mounted at /root which is infeasible for compiling the kernel and running a VM. You have to enable the internal SSD by editing the profile. You may refer to the [cloudlab manual](http://docs.cloudlab.us/advanced-storage.html) and the `e6998-vct-m400` profile.

## Install Dependencies
### Dependencies for Kernel Compilation
`sudo apt install build-essential libncurses-dev bison flex libssl-dev libelf-dev`
### Dependencies for DTB Compilation
`sudo apt install device-tree-compiler`
### Dependencies for u-boot
`sudo apt install u-boot-tools`

## Compile QEMU Modified for SeKVM
You can use the qemu source code in the artifact repo.

**Note that source code is only for running VMs on SeKVM. You should use unmodified QEMU for running VMs on vanilla KVM.**

## Compile and Install SeKVM
1. Get the SeKVM source code from the artifact repo and compile the source code
```bash
cd linux
make sekvm_defconfig && make -j8 && sudo make install && sudo make modules_install
```
2. Backup current kernel, initrd and boot script
```bash
cd /boot
cp uImage uImage.bak
cp uInitrd uInitrd.bak
cp boot.scr boot.scr.bak
```
3. Make u-boot image and install the image
```bash
cd linux
mkimage -A arm -O linux -C none -T kernel -a 0x00080000 -e 0x00080000 -n Linux
		-d arch/arm64/boot/Image arch/arm64/boot/uImage
cp arch/arm64/boot/uImage /boot/uImage
```
4. **Save the following boot script to boot.script.** The firmware on m400 only exposes a limited GICv2 interface, so we need to patch the boot script as a workaround.
```bash
setenv bootargs "console=ttyS0,${baudrate}n8r ro root=/dev/sda1 irqchip.gicv2_force_probe=1"
setenv verify no
load scsi 0 ${kernel_addr_r} uImage
load scsi 0 ${ramdisk_addr_r} uInitrd
bootm ${kernel_addr_r} ${ramdisk_addr_r} ${fdt_addr_r}
```
5. Make the boot script image
```bash
mkimage -A arm -T script -C none -n "SeKVM Boot Script" \
		-d boot.script  boot.scr
cp boot.scr /boot/. 
```
6. Install the initrd
```bash
mkimage -A arm -T ramdisk -C none -n uInitrd -d /boot/initrd.img-4.18.0+ /boot/uInitrd
```
7. Reboot the machine


## Running the VM
You can use the [script](https://github.com/VeriGu/sosp-paper211-ae/blob/master/scripts/tests/run-guest-sekvm.sh) in the artifact repo to run the VM. Since the script is assumed to be running on the provided cloudlab image, you may change the path of the QEMU to where you installed your QEMU.
