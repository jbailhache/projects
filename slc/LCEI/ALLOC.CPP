
#include "lctm.h"

/* #include "stdio.h" */

#ifdef TURBO_C
#include "dos.h"
#endif

#ifndef CPP
union REGS reg;
struct SREGS sreg;
#endif

#define NPAR 0x3000

#define SIZEPAR 0x10

char f (long i)
{
    return i & 0xFF;
}

char buf_dem[MAX_DEM*sizeof(struct S_DEM)];

#define SIZE_MCB 16

char far *alloc (long n)
{
char far *p;
long i;
long np;
    /* return (char far *)buf_dem; */
#ifdef CPP
#else
    printf ("Allocating 0x%lX blocks\n", n);
    np = (n >> 4) + 1;
    reg.h.ah = 0x48;
    reg.x.bx = np + SIZE_MCB;
    int86 (0x21, &reg, &reg);
    if (reg.x.flags & 1)
    {
        fprintf (stderr, "Error %04X allocating memory\n", reg.x.ax);
        if (reg.x.ax == 8)
            fprintf (stderr, "0x%X paras available\n", reg.x.bx);
    }
    else
    {
        p = MK_FP (reg.x.ax, 0);
        printf ("AX=%04X\n", reg.x.ax);
        printf ("p=%08lp %08lx\n", p, p);

/*
        for (i=0; i<np*SIZEPAR; i++)
            p[i] = f(i);
        for (i=0; i<np*SIZEPAR; i++)
            if (p[i] != f(i))
                printf ("Error at %08lX\n", i);
*/        
        return p+SIZE_MCB;
    }
#endif
}

free1 (char far *p)
{
#ifdef CPP
#else
    reg.h.ah = 0x49;
    sreg.es = FP_SEG(p);
    int86x (0x21, &reg, &reg, &sreg);
    if (reg.x.flags & 1)
        fprintf (stderr, "\nError 0x%04X freeing memory\n", reg.x.ax);
#endif
}

