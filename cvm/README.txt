CVM - Compiled Virtual Machine
24/08/2011 - Version for Linux, Dos, Windows Mobile and Android

All the files needed for Linux, Dos and Windows Mobile are contained in the directory cvm/jni.

For Android application (interpreted mode only) :

Build procedure :

Required : NDK and ant

- Add the following lines to cvm/jni/cvm.h :
#define INTERP 
#define JNI 

- In directory cvm, type :
ndk-build
ant debug


Installation :

A file named cvm-debuk.apk is created in directory cvm/bin. Copy it to the Android device and install it.
Copy the CVM source (for example cvm/jni/forth.cvm for the Forth interpreter) to /mnt/sdcard on the Android device.


For Android, binary executable for rooted Android device :

Build procedure : cvm/jni/build-cvm-android-interp.sh
Installation : 
- copy cvm-android to /data/local/bin on the Android device
- copy the CVM source (for example forth.cvm) somewhere on the Android device
- on the Android device, in a shell terminal, type :
cvm-android r forth.cvm

 
