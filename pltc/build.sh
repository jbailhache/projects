#!/bin/sh

# Files required :
#  - headers : config.h coroutin.h expr.h param_ex.h prolog.h stream.h 
#  - C sources : pltoc.c prolog.c expr.c schedule.c 
#  - Prolog sources : append.pro member.pro parent.pro testc.pro testcut.pro

echo "Build Prolog -> C translator pltoc ..."
cc -g -w -o pltoc pltoc.c

echo "Translate and build programs ..."
echo

for prog in append member parent testc testcut
do
 echo "Translate $prog.pro -> $prog.c ..."
 ./pltoc $prog.pro $prog.c
 echo
 echo "Build $prog ..."
 cc -g -w -DVAR_VAL -o $prog $prog.c prolog.c expr.c schedule.c
 echo "$prog built."
 echo
done

echo "All programs have been built !"

