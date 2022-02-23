#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

if [ -z `command -v dtc` ]
then
    echo "device tree compiler (dtc) not found"
    echo "on ubuntu, apt install device-tree-compiler"
fi

BOOT="https://github.com/Alasdair/sail-arm-boot/archive/master.zip"

while true; do
    read -p "Download boot files from $BOOT (y/n)? " yn
    case $yn in
	[Yy]* )
	    curl -L $BOOT 1> boot.zip;
	    break;;
	[Nn]* ) break;;
	* ) echo "Please answer yes or no.";;
    esac
done

if [ ! -f boot.zip ]
then
    echo "existing boot.zip could not be found, exiting"
    exit 1
fi

unzip -u boot.zip
mkdir -p sail-arm-boot-master/initramfs

echo "Building bootloader"
make -C sail-arm-boot-master bootloader.bin

echo "Building initramfs"
make -C sail-arm-boot-master initramfs

echo "Building device tree blob"
make -C sail-arm-boot-master sail.dtb

LINUX="https://cdn.kernel.org/pub/linux/kernel/v4.x/linux-4.14.92.tar.xz"

while true; do
    read -p "Download Linux from $LINUX (y/n)? " yn
    case $yn in
	[Yy]* )
	    wget $LINUX;
	    break;;
	[Nn]* ) break;;
	* ) echo "Please answer yes or no.";;
    esac
done

if [ ! -f linux-4.14.92.tar.xz ]
then
    echo "existing linux-4.14.92 could not be found, exiting"
    exit 1
fi

echo "Unpacking Linux"
tar -xf linux-4.14.92.tar.xz

echo "Copying config file"
cp sail-arm-boot-master/.config linux-4.14.92/

echo "Building Linux"
make -C linux-4.14.92 ARCH=arm64 CROSS_COMPILE=aarch64-linux-gnu- -k -j 8

cp linux-4.14.92/arch/arm64/boot/Image .
cp sail-arm-boot-master/bootloader.bin .
cp sail-arm-boot-master/sail.dtb .

while true; do
    read -p "Rebuild C emulator with device support (y/n)? " yn
    case $yn in
	[Yy]* )
	    rm -f c/morello.c c/morello;
	    make DEVICES=devices.sail gen_c;
	    break;;
	[Nn]* ) break;;
	* ) echo "Please answer yes or no.";;
    esac
done

if [ ! -f ./c/morello ]
then
    echo "cannot find built C emulator, exiting"
    exit 1
fi

./c/morello -b 0x80000000,bootloader.bin -b 0x81000000,sail.dtb -b 0x82080000,Image -C cpu.cpu0.RVBAR=0x80000000 2> /dev/null || true

rm -f bootloader.bin
rm -f sail.dtb
rm -f Image

exit 0
