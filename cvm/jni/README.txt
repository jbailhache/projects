CVM-Forth is a Forth compiler for the Compiled Virtual Machine CVM.

CVM is a virtual machine running a simple programming language looking like assembly language but with a syntax more similar to C. This virtual machine can be implemented either by interpreting byte code, or by compiling CVM language into machine code of a given processor.

More informations concerning CVM are in the file cvmdoc.txt.

Actually only a subset of the Forth programming language is implemented in CVM-Forth.
A documentation of this language is in the file forthdoc.txt.

The CVM source of CVM-Forth is in the file forth.cvm.

To run it :

 - Interpreted mode under Linux :
    ./cvm-linux-interp r forth.cvm

 - Interpreted mode under DOS :
    cvm-tc r forth.cvm

 - Compiled mode under DOS :
    cvm-tc c forth16.cvm forth.asm
    tasm forth
    tlink forth+cvmrtlc+cvmrtla
    forth

 - Interpreted mode under Windows :
    cvm-dev r forth.cvm
     
 - Compiled mode under DOS :
    cvm-dev c forth16.cvm forth.asm
    tasm forth
    tlink forth+cvmrtlc+cvmrtla
    forth
    
 - Pocket PC or smartphone under Windows Mobile :
    CVM-Forth runs under Pocket Console which is included in Pocket GCC. 
    First install Pocket Console, CMD, and also PGCC if you want to rebuild it, with the corresponding CAB files. Set the Windows Mobile registry key HKEY_LOCAL_MACHINE\Drivers\Console\OutputTo to 0.
    Copy the file forth.cvm to cvm.txt in the root directory of the main memory of the pocket PC.
    Copy cvm-wm-interp.exe and cvm-wm-comparm.exe anywhere in the main memory of the pocket PC (it seems it does not work in a memory card).
    Run the DOS terminal of Pocket Console.
    Run cvm-wm-interp for interpreted mode or cvm-wm-comparm for compiled mode.

A file named cvmin.txt may contain some Forth code which is compiled and executed when the compiler starts.

    



