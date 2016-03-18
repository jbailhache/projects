
#ifdef INTERP
typedef long instr;
#endif

#ifdef COMPARM
typedef int instr;
#endif

#ifdef COMPX86
typedef unsigned char instr;
#endif
