\pgcc\cc1plus \pgcc\samp\cvm\cvm.c -DPPC -DCOMPARM -o \pgcc\samp\cvm\cvm.s -I \pgcc\include -include \pgcc\fixincl.h -fms-extensions

\pgcc\as \pgcc\samp\cvm\cvm.s -o \pgcc\samp\cvm\cvm.o

\pgcc\cc1plus \pgcc\samp\cvm\asmwm.c -o \pgcc\samp\cvm\asm.s -I \pgcc\include -include \pgcc\fixincl.h -fms-extensions

\pgcc\as \pgcc\samp\cvm\asm.s -o \pgcc\samp\cvm\asm.o

\pgcc\cc1plus \pgcc\samp\cvm\dbg.c -DPPC -DCOMPARM -o \pgcc\samp\cvm\dbg.s -I \pgcc\include -include \pgcc\fixincl.h -fms-extensions

\pgcc\as \pgcc\samp\cvm\dbg.s -o \pgcc\samp\cvm\dbg.o

\pgcc\cc1plus \pgcc\samp\cvm\target.c -DPPC -DCOMPARM -o \pgcc\samp\cvm\target.s -I \pgcc\include -include \pgcc\fixincl.h -fms-extensions

\pgcc\as \pgcc\samp\cvm\target.s -o \pgcc\samp\cvm\target.o

\pgcc\ld \pgcc\samp\cvm\cvm.o \pgcc\samp\cvm\asm.o \pgcc\samp\cvm\dbg.o \pgcc\samp\cvm\target.o -o \pgcc\samp\cvm\cvm-wm-comparm.exe -L \pgcc\lib -l cpplib -l corelibc -l coredll -l aygshell -l runtime -l portlib -e main
 
