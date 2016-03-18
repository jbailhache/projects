 
#define GBLVARS
#include "cvm.h"

/* #define TRACE */

#if 0
/* #define PPC */
#define INTERP
/* #define COMPARM */
/* #define COMPX86 */

#ifndef PPC
#include <stdio.h>
#endif

#include <stdlib.h>
#include <string.h>

void printasm (char *s, unsigned int x, unsigned int adr);
void debug (void);

#define NLABELS 0x100
#define LEN 0x20

struct labels
{
	char name[LEN];
	unsigned int value;
} labels[NLABELS];


typedef unsigned char chr;
typedef char byte;

#ifdef INTERP
typedef long instr;
#endif

#ifdef COMPARM
typedef int instr;
#endif

#ifdef COMPX86
typedef unsigned char instr;
#endif
 
typedef instr *codeptr;

#ifdef CPLUSPLUS
typedef codeptr (*codefn) (codeptr, union any);
#else
typedef codeptr (*codefn)();
#endif

typedef union any
{
 long i;
 instr ins;
 long *p;
 codeptr cp;
 codefn f;
 void (*vf) (void);
 int (*intf)();
 struct word *pw;
 char *pchar;
} any;

instr cod[4000];

codeptr lab[256];

int nlab = 0;
struct label
{
	char name[LEN];
	any value;
} label[NLABELS];

struct word
{
 struct word *link;
 any code;
 any param;
 int flags;  
 chr *pname;
 chr name[4];
};

typedef struct word *pword;


pword lastword = NULL;

#define DICSIZE 1000
int dic[DICSIZE];

any freedic;
any freespace;

pword gpw;
int gwri;

codeptr c_mov_ra_im (codeptr cp, int im, char *l);
codeptr c_mov_r0_cont_ra (codeptr cp);
codeptr c_mov_ra_cont_ra (codeptr cp);

#endif

int brkdbg(int x)
{
 printf("brkdbg\n");
 return x;
}

void checkadr (instr *adr)
{
 if (adr < cod || adr >= cod + CODESIZE)
 {
  printf ("checkadr: code overflow\n");
  trace ("checkadr: code overflow");
  exit(0);
 }
}

void init_dic (void)
{
 freedic.pw = (pword)dic; 
} 

#ifdef JNI
extern char inputchar();
void output (char *s);
#else
void output (char *s) 
{
 printf ("%s", s) ;
} 
#endif 
char buf[1000];

#ifndef JNI
int trace (char *s)
{
}
#endif

chr getchr1a ()
{
 chr c;
#ifdef JNI
 /* c = *inptr++; */
 c = inputchar ();
#else
 c = getchar();
#endif
 /* lastcp = instbl+c; */
 return c;
}

chr getchr1 ()
{
 chr c;
#ifdef JNI
 if (cvmin == stdin)
 {
  c = inputchar();
  sprintf (buf, "read '%c' from input", c);
  trace (buf);
 }
 else
#endif
 {
  c = fgetc (cvmin);
  sprintf (buf, "read '%c' from cvmin", c);
  trace (buf);
 }
 if (feof(cvmin))
 {
  cvmin = stdin;
#ifdef JNI
  c = inputchar();
#else
  c = fgetc (cvmin);
#endif
  sprintf (buf, "eof: read '%c'", c);
  trace (buf);
 }
 return c;
}

/*
chr (*pgetchr) (void) = getchr1;
#define getchr (*pgetchr)
*/

void putchr (chr c)
{
#ifdef JNI
 sprintf (buf, "%c", c);
 output (buf);
#else
 putchar(c);
#endif
}

void printdec (int i)
{
 sprintf (buf, " %d ", i);;
 output (buf);
}

void printhex (int i)
{
 sprintf (buf, " %X ", i);
 output (buf);
}

/*
#define WORDSIZE 32

chr cr;
chr wr[WORDSIZE];
char awr[WORDSIZE];
*/

chr readcarac (void)
{
 cr = getchr();
/*
 printf("readcarac->%X\n",cr);
*/
 return cr;
}

int isblnk (chr c)
{
	if (c == ' ' || c == '\t' || c == '\n' || c == '\r')
		return 1;
	else
		return 0;
}

int iswordcarac (chr c)
{
	return (!isblnk(c) && c);
}

void readto (char delim, char *ptr)
{
 for (;;)
 {
  readcarac();
  if (cr==delim)
   break;
  *ptr++ = cr;
 }
 *ptr++ = 0;
}

void readword (void)
{
	int i;
	readcarac();
    if (cr==0) 
    {
       wr[0] = 0;
       awr[0] = 0;
       return ;
    }     
	/* TRACE "readword: 1st cr = '%c' %X\n", cr, cr ENDTRACE */
	while (isblnk (cr))
	{
		readcarac();
         if (cr == 0) 
         {
            wr[0] = 0;
            awr[0] = 0;
            return ;
        } 
		/* TRACE "skip blanks: cr = '%c' %X\n", cr, cr ENDTRACE */
	}
	i = 0;
	while (iswordcarac(cr))
	{
		/* TRACE "read cr = '%c' %X\n", cr, cr ENDTRACE */
		if (i >= WORDSIZE-1)
		{
			printf ("word overflow\n");
			trace ("word overflow");
			exit (0);
		}
		wr[i] = cr;
		awr[i] = cr;
		/* TRACE "awr = <%s>\n", awr ENDTRACE */
		i++;
		readcarac();
	}
	wr[i] = 0;
	awr[i] = 0;
	sscanf (awr, "%x", &gwri);
	/* TRACE "Word read: <%s>\n", awr ENDTRACE */
/*
        printf("word read: <%s> Ã\n",awr);
*/
}

void testreadword (void)
{
 for (;;)
 {
  readword();
  printf (" <%s> ", wr);
  if (!strcmp((char*)wr,"BYE"))
   break;
 }
}

int slen (chr *s)
{
 return strlen((char *)s);
}

int scmp (chr *s1, chr *s2)
{
 return strcmp ((char*)s1, (char*)s2);
}

chr * scpy (chr *s1, chr *s2)
{
 return (chr*) strcpy ((char*)s1, (char*)s2);
}

codeptr compile_pushint (codeptr cp, int x);

/*
instr *code_undef (instr *ptrcode, any p)
{
int i;
 i = 0;
 sscanf ((char *)p.s, "%d", &i);
 if (i == 0)
 {
  i = 1;
  sscanf ((char *)p.s, "%d", i);
  if (i == 1)
  {
   printf ("Undefined word: <%s>\n", (char *)p.s);
   return ptrcode;
  }
  else
  {
   ptrcode = compile_pushint (ptrcode, i);
   return ptrcode;
  }
 }
 else
 {
  ptrcode = compile_pushint (ptrcode, i);
  return ptrcode;
 }
}
*/

pword findword (chr *name)
{
	pword pw;
	char buf[1000];
	int i;
	/* TRACE "begin findword\n" ENDTRACE */
	for (i=0; name[i]; i++)
	{
		if (i>=99)
		{
			printf ("overflow in findword\n");
			trace ("overflow in findword");
			exit(0);
		}
		buf[i]=name[i];
	}
	buf[i]=0;
	/* TRACE "findword <%s>\n", buf ENDTRACE */
	pw = lastword;
	/* TRACE "loop\n" ENDTRACE */
	for (;;)
	{
#ifdef TRACE
		if (pw != NULL)
		{
		 printf ("findword <%s> : pw=%lX %d pname=<%s>\n", 
			name, pw, sizeof(pw), pw->pname);
		 gets(buf);
		}
#endif

		/* TRACE "pw=%X\n", pw ENDTRACE */
		if (pw == NULL)
		{
			/* TRACE "findword: not found\n" ENDTRACE */
			return NULL;
		}
		/* TRACE "not null\n" ENDTRACE */
		if (!scmp (name, pw->pname))
		{
			/* TRACE "findword: found\n" ENDTRACE */
			return pw;
		}
		/* TRACE "next\n" ENDTRACE */
		pw = pw->link;
	}
	return NULL;
}

pword createword (chr *name)
{
	int (*defaultop1) ();
	pword pw;
        int s;
	char buf[1000];

	/*
	printf ("word: %X %X %X %X %X\n",
	 &freedic.pw->link,
	 &freedic.pw->code,
	 &freedic.pw->param,
	 &freedic.pw->pname,
	 &freedic.pw->name);
	gets(buf);
	*/

	freedic.pw->link = lastword;

	pw = findword ((chr *)"UNDEFINED");
	if (pw == NULL)
	{
		freedic.pw->code.f = NULL;
		freedic.pw->param.pw = freespace.pw;
		/* freedic.pw->pw = 0; */
	}
	else
	{
		freedic.pw->code.f = pw->code.f;
		freedic.pw->param = pw->param;
		/* freedic.pw->pw = freespace.pw; */
	}

	/* freedic.ph->wmode=MODECP; */
	/* freedic.ph->length = slen(name); */
	freedic.pw->pname = freedic.pw->name;
	scpy (freedic.pw->name, name);
	lastword=freedic.pw;
	freedic.pchar += sizeof(struct word) + sizeof(chr) * (slen(name)+1); 
	freedic.i = ((freedic.i + 3) / 4) * 4; 
	/* freedic.i = ((freedic.i + sizeof(int)-1) / sizeof(int)) * sizeof(int); */
	/*
	s = sizeof(struct word) + sizeof(chr) * (slen(name)+1);
	freedic.pchar += ((s + 3) / 4) * 4;  
	*/
	if (freedic.p >= dic+DICSIZE)
	{
	 printf ("Dictionary overflow\n");
	 trace ("Dictionary overflow");
	 exit(0);
	}
	return lastword;
}


pword getwordstr (chr *name)
{
	pword pw;
	char aname[WORDSIZE];
	int i;
	for (i=0; name[i]; i++)
	{
		if (i >= WORDSIZE-1)
		{
			printf ("word overflow in getwordstr\n");
			trace ("word overflow in getwordstr");
			exit(0);
		}
		aname[i]=name[i];
	}
	aname[i]=0;
	/* TRACE "getword <%s>\n", aname ENDTRACE */
	pw = findword (name);
	/* printf("findword->%X\n",pw); */
	/* TRACE "pw = %X\n", pw ENDTRACE */
	if (pw != NULL)
	{
		/* TRACE "getword: found\n" ENDTRACE */
		gpw=pw;
		return pw;
	}
	/* TRACE "getword: not found\n" ENDTRACE */
	pw = createword (name);
	/* TRACE "pw=%X\n", pw ENDTRACE */
	/* TRACE "end getword\n" ENDTRACE */
	gpw = pw;
	/* printf("gpw=%X\n",gpw); */
	return pw;
}

/*
pheader getreadword (void)
{
	pheader pw;
	readword();
	pw = getword(wr);
	return pw;
}
*/

pword getword (void)
{
 pword pw;
 readword();
 if (wr[0] == 0) 

   return NULL;
 pw = getwordstr(wr);
 /* printf ("getword -> %lX\n", pw); */
 return pw;
}

/*
#define code_mov_r0_im 0x1000F
#define code_q_mov_r0_imr0 0x101000F
#define code_mov_r1_im 0x1010F
#define code_q_mov_r1_imr0 0x101010F
#define code_mov_ra_im 0x10A0F
#define code_q_mov_ra_imr0 0x1010A0F
#define code_mov_r_r 0x10000
#define code_mov_r1_r0 0x10100
#define code_q_mov_r1_r0 0x1010100
#define code_mov_r2_r0 0x10200
#define code_mov_r0_r2 0x10002
#define code_mov_r1_r2 0x10102
#define code_mov_ra_r0 0x10A00
#define code_mov_rb_r0 0x10B00
#define code_mov_rc_r0 0x10C00
#define code_mov_r0_ra 0x1000A
#define code_mov_r0_rb 0x1000B
#define code_mov_r0_rc 0x1000C
#define code_mov_ra_r1 0x10A01
#define code_mov_rc_r1 0x10C01
#define code_mov_rc_ra 0x10C0A
#define code_mov_r1_rc 0x1010C
#define code_mov_r0_cont_ra 0x1001A
#define code_mov_ra_cont_ra 0x10A1A
#define code_mov_cont_ra_r0 0x11A00
#define code_mov_r0_cont_ra_plus_im 0x1009A
#define code_mov_cont_ra_plus_im_r0 0x19A00
#define code_mov_r0_cont_rb_inc 0x1005B
#define code_mov_cont_dec_rb_r0 0x13B00
#define code_mov_r1_cont_rb_inc 0x1015B
#define code_mov_ra_cont_rb_inc 0x10A5B
#define code_mov_cont_dec_rb_r1 0x13B01
#define code_mov_cont_rc_inc_r0 0x15C00
#define code_add_r0_r1 0x20001
#define code_sub_r0_r1 0x30001
#define code_bp_depl 0xC2FFF
#define code_bz_depl 0xC3FFF
#define code_bp_ra 0xC0AFF
#define code_call_depl 0xD2FFF
#define code_call_ra 0xD0AFF
#define code_beginf 0xE0001
#define code_endf 0xE0002
#define code_ret 0xEFFFF
#define code_ror_r0 0x600FF
#define code_asr_r0 0x700FF
#define code_and_r0_r1 0x80001
#define code_xor_r0_r1 0x90001
#define code_fillmem 0xE0000
#define code_callext 0xFFF0F
#define code_getchar 0x1000FF
#define code_putchar 0x11FF00
#define code_scanhex 0x1200FF
#define code_getword 0x1300FF
#define code_setbradr 0x140000
#define code_exit 0xFFFFFF
*/

/*
FILE *f_tasm = NULL;
FILE *f_asmi = NULL;
FILE *f_asml = NULL;
FILE *f_x86 = NULL;
*/

/* char last_label; */
/* char last_label[200]; */

int f_getchar (void)
{
 return getchr();
}

void f_putchar (int c)
{
#ifdef JNI
 sprintf (buf, "%c", c);
 output (buf) ;
#else
 putchar (c);
#endif
 /* printf(" %c-%X ",c,c); */
}

void f_print (int x)
{
 sprintf(buf, " %X ",x);
 output (buf);
}

long f_scanhex (void)
{
 long x;
 x = 0;
 fscanf (cvmin, "%X", &x);
 /* printf("scanhex->%X\n",x); */
 return x;
}

void f_printhex (int x)
{
 sprintf(buf, " %X ",x);
 output (buf);
}

/* any r0, r1, r2, ra, rb, rc; */
/*
any reg[16];
#define r0 reg[0]
#define r1 reg[1]
#define r2 reg[2]
#define ra reg[10]
#define rb reg[11]
#define rc reg[12]

#define STACKSIZE 1000
codeptr stack[STACKSIZE];
int sp;
*/

/* this function is no more used and can be removed */
void interp1 (void)
{
codeptr cp;
instr ins;
int depl;
any a;
char c;
 cp = cod;
 sp = 0;
 for (;;)
 {
  ins = *cp++;
  /* printf ("rB=%08X %s\n", rb.i, instr_name(ins)); */
  /* printf ("%08X %08X\n", ins, *cp); */
  if (ins == code_mov_r0_im)
    r0.ins = *cp++;
  else if (ins == code_mov_r1_im)
    r1.ins = *cp++;
  else if (ins == code_mov_ra_im)
    ra.ins = *cp++;
  else if (ins == code_q_mov_r0_imr0)
  {
    *(rc.p++) = code_mov_r0_im;
    *(rc.p++) = r0.ins;
  }
  else if (ins == code_q_mov_r1_imr0)
  {
    *(rc.p++) = code_mov_r1_im;
    *(rc.p++) = r0.ins;
  }
  else if (ins == code_q_mov_ra_imr0)
  {
    *(rc.p++) = code_mov_ra_im;
    *(rc.p++) = r0.ins;
  }
  else if ((ins & 0xFFFFF0F0) == code_mov_r_r)
  {
    int rd, rs;
    rd = (ins & 0xFF00) >> 8;
    rs = (ins & 0xFF);
    reg[rd] = reg[rs];
  }
  else if (ins == code_mov_r1_r0)
    r1 = r0;
  else if (ins == code_mov_r2_r0)
    r2 = r0;
  else if (ins == code_mov_r0_r2)
    r0 = r2;
  else if (ins == code_mov_r1_r2)
    r1 = r2;
  else if (ins == code_q_mov_r1_r0)
    *(rc.p++) = code_mov_r1_r0;
  else if (ins == code_mov_ra_r0)
    ra = r0;
  else if (ins == code_mov_rb_r0)
    rb = r0;
  else if (ins == code_mov_rc_r0)
    rc = r0;
  else if (ins == code_mov_r0_ra)
    r0 = ra;
  else if (ins == code_mov_r0_rb)
    r0 = rb;
  else if (ins == code_mov_r0_rc)
    r0 = rc;
  else if (ins == code_mov_ra_r1)
    ra = r1;
  else if (ins == code_mov_rc_r1)
    rc = r1;
  else if (ins == code_mov_rc_ra)
    rc = ra;
  else if (ins == code_mov_r1_rc)
    r1 = rc;
  else if (ins == code_mov_r0_cont_ra)
    r0.i = *(ra.p);
  else if (ins == code_mov_ra_cont_ra)
    ra.i = *(ra.p);
  else if (ins == code_mov_cont_ra_r0)
    *(ra.p) = r0.i;
  else if (ins == code_mov_r0_cont_ra_plus_im)
  {
    /* r0.i = ra.p[((int)(*cp++))/4]; */
    r0.i = ra.p[((int)(*cp))/4];
    cp++;
  }
  else if (ins == code_mov_cont_ra_plus_im_r0)
    ra.p[((int)(*cp++))/4] = r0.i;
  else if (ins == code_mov_r0_cont_rb_inc)
   r0.i = *(rb.p++);
  else if (ins == code_mov_cont_dec_rb_r0)
  {
   /* printf ("rb.p=%X\n",rb.p); */
   *(--rb.p) = r0.i;
  }
  else if (ins == code_mov_r1_cont_rb_inc)
   r1.i = *(rb.p++);
  else if (ins == code_mov_ra_cont_rb_inc)
   ra.i = *(rb.p++);
  else if (ins == code_mov_cont_dec_rb_r1)
   *(--rb.p) = r1.i;
  else if (ins == code_mov_cont_rc_inc_r0)
   *(rc.p++) = r0.i;
  else if (ins == code_add_r0_r1)
    r0.i = r0.i + r1.i;
  else if (ins == code_sub_r0_r1)
    r0.i = r0.i - r1.i;
  else if (ins == code_bp_depl)
  {
    depl = (int) *cp++;
    if (r0.i >= 0)
     cp += depl;
  }
  else if (ins == code_bz_depl)
  {
    depl = (int) *cp++;
    if (r0.i == 0)
     cp += depl;
  }
  else if (ins == code_bp_ra)
  {
    if (r0.i >= 0)
     cp = ra.cp;
  }
  else if (ins == code_bz_ra)
  {
    if (r0.i == 0)
     cp = ra.cp;
  }
  else if (ins == code_setbradr)
  {
   /* rA = adresse de l'instruction de saut bp
      r0 = adresse du saut */
   int depl;
   depl = r0.cp - ra.cp - 2;
   ra.cp[1] = depl;
   /* printf ("setbradr: rA=%X r0=%X depl=%X\n", ra.cp, r0.cp, depl); */
  }
  else if (ins == code_call_depl)
  {
    if (sp>=STACKSIZE)
    {
     printf("\nstack overflow\n");
     break;
    }
    depl = (int) *cp++;
    stack[sp++] = cp;
    cp += depl;
  }
  else if (ins == code_call_ra)
  {
    if (sp >= STACKSIZE)
    {
     printf ("\nstack overflow\n");
     /* exit(0); */
     return;
    }
    stack[sp++] = cp;
    cp = ra.cp;
  }
  else if (ins==code_beginf);
  else if (ins == code_ret || ins==code_endf)
  {
    if (sp <= 0)
    {
     printf ("\nstack underflow\n");
     /* exit(0); */
     return;
    }
    cp = stack[--sp];
  }
  else if (ins == code_asr_r0)
    r0.i = r0.i >> 1;
  else if (ins == code_and_r0_r1)
    r0.i = r0.i & r1.i;
  else if (ins == code_xor_r0_r1)
    r0.i = r0.i ^r1.i;
  else if (ins == code_callext)
  {
    a.ins = *cp++;
    a.vf();
  }
  else if (ins == code_callext_ra)
  {
    ra.vf();
  }
  else if (ins == code_getchar)
    r0.i = getchar();
  else if (ins == code_putchar)
    putchar (r0.i);
  else if (ins == code_getword)
  {
    ra.pw = getword();
    r0.i = 0;
    sscanf (awr, "%x", &r0.i);
  }
  else if (ins == code_scanhex)
    r0.i = f_scanhex ();
  else if (ins == code_printhex)
   f_printhex (r0.i);
  else if (ins == code_fillmem)
  {
   int n, i;
   n = (int)(*cp++);
   for (i=0; i<n; i++)
    *(rc.cp++) = *cp++;
  }
  else if (ins == code_dumpcode)
   dmpcode();
  else if (ins == code_exit)
   exit(r0.i);
  else
    printf ("Instruction %X not implemented\n", ins);

 }

}

#if 0
codeptr compile_prog1 (codeptr cp)
{
 cp = c_getchar (cp);
 cp = c_mov_r1_r0 (cp);
 cp = c_mov_r0_im (cp, 1, 0);
 cp = c_add_r0_r1 (cp);
 cp = c_putchar (cp);
 cp = c_ret (cp);
 return cp;
}

codeptr compile_prog (codeptr cp)
{
 codeptr from, to, adr1, adr2, adr3, adr4;
 /* cp = c_mov_r0_im (cp, 1); */
 /* cp = c_mov_r1_r0 (cp); */
 cp = c_getchar(cp);
 adr1 = cp;
 cp = c_mov_ra_im (cp, 0, 0);
 cp = c_mov_cont_ra_r0 (cp);
 to = cp;
 printf ("to=%X\n",to);
 adr2 = cp;
 cp = c_mov_ra_im (cp, 0, 0);
 cp = c_mov_r0_cont_ra (cp);
 cp = c_mov_r1_im (cp, 1, 0);
 cp = c_sub_r0_r1 (cp);
 adr3 = cp;
 cp = c_mov_ra_im (cp, 0, 0);
 cp = c_mov_cont_ra_r0 (cp);
 cp = c_putchar (cp);
 /* cp = c_print (cp); */
 /* cp = c_mov_r1_im (cp, 0xff); */
 /* cp = c_and_r0_r1 (cp); */
 /* cp = c_mov_r0_im (cp, -1); */
 adr4 = cp;
 cp = c_mov_ra_im (cp, 0, 0);
 cp = c_mov_r0_cont_ra (cp);
 /* from = cp+1; */
 from = cp;
 printf("from=%X\n",from);
 cp = c_bp_depl (cp, 0);
 printf("from=%X to=%X\n",from,to);
 setbradr (from, to);
 cp = c_ret (cp);
 c_mov_r1_im (adr1, (int)cp, 0);
 c_mov_r1_im (adr2, (int)cp, 0);
 c_mov_r1_im (adr3, (int)cp, 0);
 c_mov_r1_im (adr4, (int)cp, 0);
 return cp;
}
#endif

int isdgt (char c)
{
 if (c>='0' && c<='9')
  return 1;
 if (c>='A' && c<='F')
  return 1;
 return 0;
}

codeptr compile_op (codeptr cp, char *op, int nargs, long *iargs, char largs[8][200], char *s)
{
int i;
codeptr from, to;
any a;
char buf[1000];
 
#ifdef TRACE
 printf ("cp=0x%X op=<%s>" , cp, op);
 for (i=0; i<nargs; i++)
  printf (" arg%d=%X", i, iargs[i]);
 printf ("\n");
#endif
 if (cp >= cod + CODESIZE)
 {
  printf ("code overflow\n");
  trace ("code overflow");
  exit(0);
 }
 if (op[0] == ':')
 {
  char name[200];
  lab[op[1]] = cp;
#ifdef TRACE
  printf ("label %c = 0x%X, cod=0x%X, depl=0x%X\n", op[1], cp, cod, cp-cod);
#endif
  sscanf (op+1, "%s", name);
  strcpy (label[nlab].name, name);
  /* printf ("label: cp=%lX\n",cp); */
  label[nlab].value.cp = cp;
  /* printf ("label: %lX %lX %lX\n", 
   cp, label[nlab].value.cp, label[nlab].value.i);*/
  /*
  printf ("cp=%lX ",cp);
  printf ("value.cp=%lX ", label[nlab].value.cp);
  printf ("value.i=%lX ", label[nlab].value.i);
  printf ("size=%d\n",sizeof(label[nlab].value.i));
  */
  nlab++;
  if (nlab >= NLAB)
  {
   printf ("Too much labels\n");
   trace ("Too much labels");
   exit(0);
  }
  if (f_tasm != NULL)
   fprintf (f_tasm, "%s:\n", name);
  if (f_asmi != NULL)
   fprintf (f_asmi, "%s:\n", name);
  if (f_asml != NULL)
   fprintf (f_asml, "%s:\n", name);
  if (f_x86 != NULL)
   fprintf (f_x86, "%s:\n", name);
  /*
  if (f_tasm != NULL)
   fprintf (f_tasm, "%c:\n", op[1]);
  if (f_asmi != NULL)
   fprintf (f_asmi, "%c:\n", op[1]);
  if (f_asml != NULL)
   fprintf (f_asml, "%c:\n", op[1]);
  if (f_x86 != NULL)
   fprintf (f_x86, "%c:\n", op[1]);
  */
 }
 else if (!strcmp (op, "align"))
 {
  if (f_tasm != NULL)
   fprintf (f_tasm, " align %d\n", iargs[0]);
  if (f_asmi != NULL)
   fprintf (f_asmi, " .align %d\n", iargs[0]);
  if (f_asml != NULL)
   fprintf (f_asml, " .align %d\n", iargs[0]);
  if (f_x86 != NULL)
   fprintf (f_x86, " .align %d\n", iargs[0]);
/*#ifndef INTERP*/
  a.cp = cp;
  a.i = (a.i + iargs[0] - 1) / iargs[0] * iargs[0];
  a.i = (a.i + sizeof(instr) - 1) / sizeof(instr) * sizeof(instr);
  return a.cp;
/*#endif*/
 }
 else if (!strcmp (op, "res"))
 {
  if (f_tasm != NULL)
   fprintf (f_tasm, " db 0%Xh dup (0)\n", iargs[0]);
  if (f_asmi != NULL)
   fprintf (f_asmi, " .space 0x%X, 0\n", iargs[0]);
  if (f_asml != NULL)
   fprintf (f_asml, " .space 0x%X, 0\n", iargs[0]);
  if (f_x86 != NULL)
   fprintf (f_x86, " .space 0x%X, 0\n", iargs[0]);
  a.cp = cp;
  a.i += iargs[0];
  /* a.i = (a.i + sizeof(instr) - 1) / sizeof(instr) * sizeof(instr); */
  return a.cp;
 }
 else if (!strcmp(op,"db"))
 {
  if (f_tasm != NULL)
   fprintf (f_tasm, " db 0%Xh\n", iargs[0]);
  a.cp = cp;
  *a.pchar++ = iargs[0];
  return a.cp;
 }
 else if (!strcmp(op,"dw"))
 {
  if (f_tasm != NULL)
   fprintf (f_tasm, " dw 0%Xh\n", iargs[0]);
  a.cp = cp;
  *a.p++ = iargs[0];
  return a.cp;
 }
#if 0
 else if (!strncmp (op, "defword", 7))
 {
  /* a verifier */

  union
  {
   codeptr cp;
   void far * far *p;
   pword pw;
   char far *pchar;
   chr far *pchr;
  } u;

  pword pw;
  int nc, nw;
  char name[100];
  sscanf (s+8,"%s",name);
  pw = (pword)cp;
  /*
  readword();
  nc = strlen(awr);
  */
  /* getwordstr(s+8); */
  nc = strlen(name);
  nw = nc/4 + 1;
  u.cp = cp;
  *(u.p) = (void far *)lastword;
  lastword = u.pw;
  u.p++;
  *(u.p)++ = (void *)(u.pw+4+nw);
  *(u.p)++ = NULL;
  *(u.p)++ = (void *)(u.pw+4);
  strcpy (u.pchar, name);
  return (codeptr)(pw+4+nw);
 }
#endif
 else if (!strcmp (op, "r="))
 {
  /* printf("op r=\n"); */
#ifdef TRACE
  printf ("im=%08lX\n", iargs[1]);
  /* gets(buf); */
#endif
  if (iargs[0]==0)
   cp = c_mov_r0_im (cp, iargs[1], largs[1]);
  else if (iargs[0]==1)
   cp = c_mov_r1_im (cp, iargs[1], largs[1]);
  else if (iargs[0]==10)
  {
   /* printf("op rA=\n"); */
   cp = c_mov_ra_im (cp, iargs[1], largs[1]);
   /* printf("end rA=\n"); */
  }
  else
   printf ("Invalid instruction <%s>\n", s);
  /* printf("end r=\n"); */
 }
 else if (!strcmp (op, "r=sva"))
 {
  if (iargs[0] == 10)
   cp = c_mov_ra_sva (cp);
  else
   printf ("Invalid instruction <%s>\n", s);
 }
 else if (!strcmp (op, "coder={r}"))
 {
  if (iargs[0]==0 && iargs[1]==0)
   cp = c_q_mov_r0_imr0 (cp);
  else if (iargs[0]==1 && iargs[1]==0)
   cp = c_q_mov_r1_imr0 (cp);
  else if (iargs[0]==10 && iargs[1]==0)
   cp = c_q_mov_ra_imr0 (cp);
  else
   printf ("Invalid instruction <%s>\n", s);
 }
 else if (!strcmp (op, "r=r"))
 {
  cp = c_mov_r_r (cp, iargs[0], iargs[1]);
  /*
  if (iargs[0]==1 && iargs[1]==0)
   cp = c_mov_r1_r0 (cp);
 
  else
   printf ("Invalid instruction <%s>\n", s);
  */
 }
 else if (!strcmp (op, "'r=r"))
 {
  if (iargs[0]==1 && iargs[1]==0)
   cp = c_q_mov_r1_r0 (cp);
  else
   printf ("Invalid instruction <%s>\n", s);
 }
 else if (!strcmp (op, "r=[r]"))
 {
  if (iargs[0]==0 && iargs[1]==10)
   cp = c_mov_r0_cont_ra (cp);
  else if (iargs[0]==10 && iargs[1]==10)
   cp = c_mov_ra_cont_ra (cp);
  else
   printf ("Invalid instruction <%s>\n", s);
 }
 else if (!strcmp (op, "r=byte[r]"))
 {
  if (iargs[0]==0 && iargs[1]==10)
   cp = c_mov_r0_byte_cont_ra (cp);
 else
  printf ("Invalid instruction <%s>\n");
 }
 else if (!strcmp (op, "[r]=r"))
 {
  if (iargs[0]==10 && iargs[1]==0)
   cp = c_mov_cont_ra_r0 (cp);
  else
   printf ("Invalid instruction <%s>\n", s);
 }
 else if (!strcmp (op, "byte[r]=r"))
 {
  if (iargs[0]==10 && iargs[1]==0)
   cp = c_mov_byte_cont_ra_r0 (cp);
  else
   printf ("Invalid instruction <%s>\n", s);
 }
 else if (!strcmp (op, "r=[r+]"))
 {
  if (iargs[0]==0 && iargs[1]==10)
   cp = c_mov_r0_cont_ra_plus_im (cp, iargs[2]);
  else
   printf ("Invalid instruction <%s>\n", s);
 }
 else if (!strcmp (op, "[r+]=r"))
 {
  if (iargs[0]==10 && iargs[2]==0)
   cp = c_mov_cont_ra_plus_im_r0 (cp, iargs[1]);
  else
   printf ("Invalid instruction <%s>\n", s);
 }
 else if (!strcmp (op, "r=[r++]"))
 {
  if (iargs[0]==0 && iargs[1]==11)
   cp = c_mov_r0_cont_rb_inc (cp);
  else if (iargs[0]==1 && iargs[1]==11)
   cp = c_mov_r1_cont_rb_inc (cp);
  else if (iargs[0]==10 && iargs[1]==11)
   cp = c_mov_ra_cont_rb_inc (cp);
  else
   printf ("Invalid instruction <%s>\n", s);
 }
 else if (!strcmp (op, "[--r]=r"))
 {
  if (iargs[0]==11 && iargs[1]==0)
   cp = c_mov_cont_dec_rb_r0 (cp);
  else if (iargs[0]==11 && iargs[1]==1)
   cp = c_mov_cont_dec_rb_r1 (cp);
  else
   printf ("Invalid instruction <%s>\n", s);
 }
 else if (!strcmp (op, "[r++]=r"))
 {
  if (iargs[0]==12 && iargs[1]==0)
   cp = c_mov_cont_rc_inc_r0 (cp);
  else
   printf ("Invalid instruction <%s>\n", s);
 }
 else if (!strcmp (op, "r=retadr"))
 {
  if (iargs[0]==0)
   cp = c_mov_r0_retadr (cp);
  else
   printf ("Invalid instruction <%s>\n", s);
 }
 else if (!strcmp (op, "retadr=r"))
 {
  if (iargs[0]==0)
   cp = c_mov_retadr_r0 (cp);
  else
   printf ("Invalid instruction <%s>\n", s);
 }
 else if (!strcmp (op, "r=lastword"))
 {
  if (iargs[0]==0)
   cp = c_mov_r0_lastword (cp);
  else
   printf ("Invalid instruction <%s>\n", s);
 }
 else if (!strcmp (op, "lastword=r"))
 {
  if (iargs[0]==0)
   cp = c_mov_lastword_r0 (cp);
  else
   printf ("Invalid instruction <%s>\n", s);
 }
 else if (!strcmp (op, "r=freedic"))
 {
  if (iargs[0]==0)
   cp = c_mov_r0_freedic (cp);
  else
   printf ("Invalid instruction <%s>\n", s);
 }
 else if (!strcmp (op, "freedic=r"))
 {
  if (iargs[0]==0)
   cp = c_mov_freedic_r0 (cp);
  else
   printf ("Invalid instruction <%s>\n", s);
 }
 else if (!strcmp (op, "r=r+r"))
 {
  if (iargs[0]==0 && iargs[1]==0 && iargs[2]==1)
   cp = c_add_r0_r1 (cp);
  else
   printf ("Invalid instruction <%s>\n", s);
 }
 else if (!strcmp (op, "r=r-r"))
 {
  if (iargs[0]==0 && iargs[1]==0 && iargs[2]==1)
   cp = c_sub_r0_r1 (cp);
  else
   printf ("Invalid instruction <%s>\n", s);
 }
 else if (!strcmp (op, "r=r*r"))
 {
  if (iargs[0]==0 && iargs[1]==0 && iargs[2]==1)
   cp = c_mul_r0_r1 (cp);
  else
   printf ("Invalid instruction <%s>\n", s);
 }
 else if (!strcmp (op, "asrr"))
 {
  if (iargs[0]==0)
   cp = c_asr_r0 (cp);
  else
   printf ("Invalid instruction <%s>\n");
 }
 else if (!strcmp (op, "r=r&r"))
 {
  if (iargs[0]==0 && iargs[1]==0 && iargs[2]==1)
   cp = c_and_r0_r1 (cp);
  else
   printf ("Invalid instruction <%s>\n", s);
 }
 else if (!strcmp (op, "r=r^r"))
 {
  if (iargs[0]==0 && iargs[1]==0 && iargs[2]==1)
   cp = c_xor_r0_r1 (cp);
  else
   printf ("Invalid instruction <%s>\n", s);
 }
 else if (!strcmp (op, "pushr"))
 {
  if (iargs[0]==0)
   cp = c_push_r0 (cp);
  else
   printf ("Invalid instruction <%s>\n", s);
 }
 else if (!strcmp (op, "popr"))
 {
  if (iargs[0]==0)
   cp = c_pop_r0 (cp);
  else
   printf ("Invalid instruction <%s>\n");
 }
 else if (!strcmp (op, "bp"))
 {
  from = cp;
  cp = c_bp_depl (cp, 0);
  setbradr (from, (codeptr)(iargs[0]));
 }
 else if (!strcmp (op, "bz"))
 {
  from = cp;
  cp = c_bz_depl (cp, 0);
  setbradr (from, (codeptr)(iargs[0]));
 }
 else if (!strcmp (op, "bpr"))
 {
  if (iargs[0]==10)
   cp = c_bp_ra (cp);
  else
   printf ("Invalid instruction <%s>\n", s);
 }
 else if (!strcmp (op, "bzr"))
 {
  if (iargs[0]==10)
   cp = c_bz_ra (cp);
  else
   printf ("Invalid instruction <%s>\n", s);
 }
 else if (!strcmp (op, "call"))
 {
  from = cp;
  cp = c_call_depl (cp, 0);
  setbradr (from, (codeptr)(iargs[0]));
 }
/*
 else if (!strcmp (op, "call{r}"))
 {
  cp = c_q_call_imr0 (cp);
 }
*/
 else if (!strcmp (op, "callr"))
 {
  if (iargs[0]==10)
   cp = c_call_ra (cp);
  else
   printf ("Invalid instruction <%s>\n", s);
 }
 else if (!strcmp (op, "callextr"))
 {
  if (iargs[0]==10)
   cp = c_callext_ra (cp);
  else
   printf ("Invalid instruction <%s>\n", s);
 }
 else if (!strcmp(op,"beginf"))
  cp=c_beginf(cp);
 else if (!strcmp(op,"endf"))
  cp=c_endf(cp);
 else if (!strcmp (op, "ret"))
  cp = c_ret (cp);

 else if (!strcmp (op, "getchar"))
 {
  /* printf("before getchar cp=%X\n",cp); */
  cp = c_getchar (cp);
  /* printf("after getchar cp=%X\n",cp); */
 }
 else if (!strcmp (op, "intbios"))
  cp = c_intbios (cp, iargs[0]);
 else if (!strcmp (op, "putchar"))
  cp = c_putchar (cp);
 else if (!strcmp (op, "scanhex"))
  cp = c_scanhex (cp);
 else if (!strcmp (op, "printhex"))
  cp = c_printhex (cp);
 else if (!strcmp (op, "getword"))
  cp = c_getword (cp);
 else if (!strcmp (op, "getwordstr"))
  cp = c_getwordstr (cp);
 else if (!strcmp (op, "fopen"))
  cp = c_fopen (cp);
 else if (!strcmp (op, "fclose"))
  cp = c_fclose (cp);
 else if (!strcmp (op, "fgetc"))
  cp = c_fgetc (cp);
 else if (!strcmp (op, "fputc"))
  cp = c_fputc (cp);

#ifdef SOCKET
 else if (!strcmp (op, "socket"))
  cp = c_socket (cp);
 else if (!strcmp (op, "closesocket"))
  cp = c_closesocket (cp);
 else if (!strcmp (op, "listen"))
  cp = c_listen (cp);
 else if (!strcmp (op, "accept"))
  cp = c_accept (cp);
 else if (!strcmp (op, "bind"))
  cp = c_bind (cp);
 else if (!strcmp (op, "connect"))
  cp = c_connect (cp);
 else if (!strcmp (op, "recv"))
  cp = c_recv (cp);
 else if (!strcmp (op, "send"))
  cp = c_send (cp);
#endif

#ifdef JNI
 else if (!strcmp (op, "findclass"))
  cp = c_findclass (cp);
 else if (!strcmp (op, "getmethodid"))
  cp = c_getmethodid (cp);
 else if (!strcmp (op, "callmethoda"))
  cp = c_callmethoda (cp);
 else if (!strcmp (op, "getstringutfchars"))
  cp = c_getstringutfchars (cp);
 else if (!strcmp (op, "newstringutf"))
  cp = c_newstringutf (cp);

#endif
 else if (!strcmp (op, "resetdraw"))
 {
  trace ("c_resetdraw ...");
  cp = c_resetdraw (cp);
 }
 else if (!strcmp (op, "draw"))
 {
  trace ("c_draw ...");
  cp = c_draw (cp);
 }
 else if (!strcmp (op, "invalidate"))
 {
  trace ("c_invalidate ...");
  cp = c_invalidate (cp); 
 }




 else if (!strcmp (op, "getprocadr"))
  cp = c_getprocadr (cp);
 else if (!strcmp (op, "code"))
  cp = c_code (cp);
 else if (!strcmp (op, "endcode"))
  cp = c_endcode (cp);
 else if (!strcmp (op, "setbradr"))
  cp = c_setbradr (cp);
 else if (!strcmp(op,"dumpcode"))
  cp=c_dumpcode(cp);
 else if (!strcmp(op,"calldummy"))
  cp=c_call_dummy(cp);
 else if (!strcmp(op,"dummyprint"))
  cp=c_dummyprint(cp);
 else if (!strcmp(op,"initcvm"))
  cp=c_initcvm(cp);
 else if (!strcmp(op,"sscandec"))
  cp=c_sscandec(cp);
 else if (!strcmp(op,"printdec"))
  cp=c_printdec(cp);
 else if (!strcmp (op, "brkdbg"))
  cp = c_brkdbg (cp);
 else if (!strcmp (op, "exit"))
  cp = c_exit (cp);
 else if (!strcmp (op, ""));
 else
 {
  printf ("Invalid instruction <%s>\n", s);
  sprintf (buf, "Invalid instruction (%s) op=(%s)", s, op);
  trace (buf);
 } 
#ifdef TRACE
 printf("end compile_op\n");
#endif
 if (cp >= cod+CODESIZE)
 {
  printf ("Code overflow\n");
  exit(0);
 }
 return cp;
}

long value_of_label (char *name)
{
 int i;
 long v;
 for (i=0; i<nlab; i++)
  if (!strcmp (label[i].name, name))
  {
   v = (long) label[i].value.cp;
   /* printf ("value_of_label = %lX %d\n", v, sizeof(label[i].value.i)); */
   return v;
  }
 return 0;
}

codeptr compile_string (codeptr cp, char *s)
{
int i, k, nargs, lop;
char op[100], args[8][10];
long iargs[8];
/* char largs[8]; */
char largs[8][200];
any a;
 if (cp >= cod + CODESIZE)
 {
  printf ("code overflow in compile_string\n");
  trace ("code overflow in compile_string");
  exit(0);
 }
 if (!strncmp (s, "tasm ", 5))
 {
  if (f_tasm != NULL)
   fprintf (f_tasm, "%s\n", s+5);
  return cp;
 }
 if (!strncmp (s, "rem ", 4))
  return cp;
 if (!strncmp (s, "ascii ",6))
 {
  s[strlen(s)-1]=0;
  if (s[strlen(s)-1]==10 || s[strlen(s)-1]==13)
   s[strlen(s)-1]=0;
  if (f_tasm != NULL)
   fprintf (f_tasm, " db \"%s\",0\n", s+6);
  a.cp = cp;
  strcpy (a.pchar, s+6);
  a.pchar += strlen(s+6)+1;
  return a.cp;
 }
 if (!strncmp (s, "unicode ", 8))
 {
  s[strlen(s)-1]=0;
  if (s[strlen(s)-1]==10 || s[strlen(s)-1]==13)
   s[strlen(s)-1]=0;
  if (f_tasm != NULL)
  {
   fprintf (f_tasm, " db ");
   for (i=8; s[i]; i++)
    fprintf (f_tasm, "0%Xh, 0, ", s[i]);
   fprintf (f_tasm, "0, 0\n");
  }
  a.cp = cp;
  for (i=8; s[i]; i++)
  {
   *a.pchar++ = s[i];
   *a.pchar++ = 0;
  }
  *a.pchar++ = 0;
  *a.pchar++ = 0;
  return a.cp;
 }
 if (!strncmp (s, "defword ", 8))
 {
   /* a verifier */

  union
  {
   codeptr cp;
   void far * far *p;
   long far *pl;
   pword pw;
   char far *pchar;
   chr far *pchr;
  } u;

  pword pw;
  int nc, nw;
  char name[100];
  sscanf (s+8,"%s",name);
#ifdef TRACE
  printf ("defword <%s>\n", name);
#endif

  if (f_tasm != NULL)
  {
   /* printf ("nw=%d\n",nw);*/
   gnw++;
   fprintf (f_tasm, "align 4\n");
   if (gnw == 1)
    fprintf (f_tasm, "w1: dw 0\n");
   else
    fprintf (f_tasm, "w%d: dw w%d\n", gnw, gnw-1);
   fprintf (f_tasm, " dw 0\n");
   fprintf (f_tasm, " dw c%d\n", gnw);
   fprintf (f_tasm, " dw 0\n");
   fprintf (f_tasm, " dw 0\n");
   fprintf (f_tasm, " dw 0\n");

   fprintf (f_tasm, " dw 0\n");
   fprintf (f_tasm, " dw 0\n");

   fprintf (f_tasm, " dw n%d\n", gnw);
   fprintf (f_tasm, " dw 0\n");
   fprintf (f_tasm, "n%d: db '%s'\n", gnw, name);
   fprintf (f_tasm, " db 0\n");
   fprintf (f_tasm, " align 4\n");
   fprintf (f_tasm, "c%d:\n", gnw); 
  }

  pw = (pword)cp;
  /*
  readword();
  nc = strlen(awr);
  */
  /* getwordstr(s+8); */
  nc = strlen(name);
  nw = nc/4 + 1;
  u.cp = cp;
  /* *(u.p) = (void *)lastword; */
  *(u.pl) = (long)lastword;
  lastword = u.pw;
  u.pl++;
  /* *(u.p)++ = (void *)(u.pw+4+nw); */
  /* *(u.p)++ = (void *)(u.pchar+12+4*nw); */
  *(u.pl)++ = (long) (u.pchar+16+4*nw);
  /* *(u.p)++ = NULL; */
  *(u.pl)++ = 0;
  *(u.pl)++ = 0;
  /* *(u.p)++ = (void *)(u.pw+4); */
  /* *(u.p)++ = (void *)(u.pchar+4); */
  *(u.pl)++ = (long)(u.pchar+4);
  strcpy (u.pchar, name);
  /* return (codeptr)(pw+4+nw); */
  return (codeptr)(u.pchar+4*nw);

 }
 for (i=0; i<8; i++)
  largs[i][0] = 0;
#ifdef TRACE
 printf ("%s", s);
#endif
 nargs = 0;
 lop = 0;
 for (i=0; s[i]!=0 && s[i]!='\n' && s[i]!='\r' && s[i]!='%'; i++)
 {
  if (s[i]!=' ' && s[i]!='\t')
  {
   if (isdgt(s[i]))
   {
    for (k=0; isdgt(s[i+k]); k++)
     args[nargs][k] = s[i+k];
    args[nargs][k] = 0;
    nargs++;
    i += k-1;
   }
   else if (s[i] == '@')
   {
    char name[200];
    i++;
    /*
    largs[nargs] = s[i];
    sprintf (args[nargs++], "%X", lab[s[i]]);
    last_label = s[i];
    */
    sscanf (s+i, "%s", name);
    i += strlen(name);
    strcpy (largs[nargs], name);
    sprintf (args[nargs], "%lX", value_of_label (name));
    /* printf ("arg=<%s>\n", args[nargs]); */
    nargs++;
    strcpy (last_label, name);
   }
   else
   {
    op[lop++] = s[i];
   }
  }
 }
 op[lop]=0;
 /*
 printf ("op=<%s>" , op);
 for (i=0; i<nargs; i++)
  printf (" arg %d = <%s>", i, args[i]);
 printf ("\n");
 */
 for (i=0; i<nargs; i++)
 {
  sscanf (args[i], "%lX", &(iargs[i]));
#ifdef TRACE
  printf ("i=%d args[i]=<%s> iargs[i]=%08lX\n", i, args[i], iargs[i]);
#endif
 }
 cp = compile_op (cp, op, nargs, iargs, largs, s);
 return cp;
}

void asm_call_ext (char *);
void dumpdebug (void)
{
 unsigned char far *p;
 int i;
 p = (unsigned char far *)asm_call_ext;
 printf ("%04X:",p);
 for (i=0; i<20; i++)
 {
  printf (" %02X", p[i]);
  fflush(stdout);
 }
 printf ("\n");
}

codeptr compile_file (codeptr cp, const char *fn,
 const char *fn_tasm, const char *fn_asmi, const char *fn_asml, const char *fn_x86)
{
FILE *f;
char line[1000];
 printf ("compile file %s\n", fn);
 f = fopen (fn, "r");
 if (f == NULL)
 {
  printf ("Cannot open file <%s>\n", fn);
  exit(0);
 }

 if (fn_tasm == NULL)
  f_tasm = NULL;
 else
  f_tasm = fopen (fn_tasm, "w");

 if (fn_asmi == NULL)
  f_asmi = NULL;
 else
  f_asmi = fopen (fn_asmi, "w");

 if (fn_asml == NULL)
  f_asml = NULL;
 else
  f_asml = fopen (fn_asml, "w");

 if (fn_x86 == NULL)
  f_x86 = NULL;
 else
  f_x86 = fopen (fn_x86, "w");

 if (f_tasm != NULL)
 {
  fprintf (f_tasm, ".model tiny\n");
  fprintf (f_tasm, ".stack 07000h\n");
  /* fprintf (f_tasm, "public _lw\n"); */
  fprintf (f_tasm, "extrn _scanhex\n");
  fprintf (f_tasm, "extrn _printhex\n");
  fprintf (f_tasm, "extrn _sscandec\n");
  fprintf (f_tasm, "extrn _printdec\n");
  fprintf (f_tasm, "extrn _getword\n");
  fprintf (f_tasm, "extrn _f_fopen\n");
  fprintf (f_tasm, "extrn _f_fclose\n"); 
  fprintf (f_tasm, "extrn _f_fgetc\n");
  fprintf (f_tasm, "extrn _f_fputc\n");
  fprintf (f_tasm, "extrn _fillmem\n");
  fprintf (f_tasm, "extrn _dmpcode\n");
  fprintf (f_tasm, "extrn _initcvm\n");
  fprintf (f_tasm, "extrn _getsva\n");
  /* fprintf (f_tasm, "public _lw\n"); */
  fprintf (f_tasm, ".code\n");
  fprintf (f_tasm, "start proc\n");
  fprintf (f_tasm, " mov ax,cs\n");
  fprintf (f_tasm, " mov ds,ax\n");
  fprintf (f_tasm, " mov ss,ax\n");
  fprintf (f_tasm, " mov es,ax\n");
  fprintf (f_tasm, " mov ax,07000h\n");
  fprintf (f_tasm, " mov sp,ax\n");
  fprintf (f_tasm, " call main\n");
  fprintf (f_tasm, " mov ah,0\n");
  fprintf (f_tasm, " int 21h\n");
  fprintf (f_tasm, "start endp\n");
  /* fprintf (f_tasm, "_lw: dw 0\n"); */
  fprintf (f_tasm, "sax: dw 0\n");
  fprintf (f_tasm, "sdx: dw 0\n");
  fprintf (f_tasm, "scx: dw 0\n");
  fprintf (f_tasm, "ssi: dw 0\n");
  fprintf (f_tasm, "sbx: dw 0\n");
  fprintf (f_tasm, "sdi: dw 0\n");
  fprintf (f_tasm, "main proc\n");
 }

 if (f_asmi != NULL)
 {
  fprintf (f_asmi, " .intel_syntax\n");
  fprintf (f_asmi, " .text\n");
/*
  fprintf (f_asml, ".globl start\n");
  fprintf (f_asml, " .type start, function\n");
  fprintf (f_asml, "start:\n");
  fprintf (f_asml, " mov %%cs,%%ax\n");
  fprintf (f_asml, " mov %%ax,%%ds\n");
  fprintf (f_asml, " call main\n");
  fprintf (f_asml, " ret\n");
*/
  fprintf (f_asmi, ".globl main\n");
  fprintf (f_asmi, " .type main, @function\n");
  fprintf (f_asmi, "main:\n");
  fprintf (f_asmi, " mov %%ax,%%cs\n");
  fprintf (f_asmi, " mov %%ds,%%ax\n");

 }

 if (f_asml != NULL)
 {
  fprintf (f_asml, " .text\n");
  fprintf (f_asml, ".globl start\n");
  fprintf (f_asml, " .type start, @function\n");
  fprintf (f_asml, "start:\n");
  fprintf (f_asml, " mov %%cs,%%ax\n");
  fprintf (f_asml, " mov %%ax,%%ds\n");
  fprintf (f_asml, " call main\n");
  fprintf (f_asml, " ret\n");
  fprintf (f_asml, ".globl main\n");
  fprintf (f_asml, " .type main, @function\n");
  fprintf (f_asml, "main:\n");
 }

 if (f_x86 != NULL)
 {
  fprintf (f_x86, " .text\n");
/*
  fprintf (f_x86, ".globl start\n");
  fprintf (f_x86, " .type start, @function\n");
  fprintf (f_x86, "start:\n");
  fprintf (f_x86, " .byte 0x8C, 0xC8, 0x8E, 0xD8\n");
  fprintf (f_x86, " call main\n");
  fprintf (f_x86, " .byte 0xC3\n");
*/
  fprintf (f_x86, ".globl main\n");
  fprintf (f_x86, " .type main, @function\n");
  fprintf (f_x86, "main:\n");
  fprintf (f_x86, " .byte 0x8C, 0xC8, 0x8E, 0xD8\n");
 }

 printf ("cod=%X cp=%X\n", cod, cp);
 for (;;)
 {
  fgets (line, sizeof(line), f);
  if (feof(f))
   break;
#ifdef TRACE
  printf ("Line to compile: %s", line);
#endif  
  cp = compile_string (cp, line);
  /* dumpdebug(); */
  if (cp >= cod+CODESIZE)
  {
   printf ("Code overflow\n");
   exit(0);
  }
 }

 if (f_tasm != NULL)
 {
  /*
  fprintf (f_tasm, " mov ah,0\n");
  fprintf (f_tasm, " int 21h\n");
  */
  fprintf (f_tasm, "main endp\n");
  fprintf (f_tasm, "end start\n");
  fclose (f_tasm);
  f_tasm = NULL;
 }

 if (f_asml != NULL)
 {
  fprintf (f_asml, "\n");
 }

 return cp;
}


void init (void)
{
int i;
#ifdef LINUXCOMP
 cod = mmap (NULL, CODESIZE*sizeof(instr), 
  PROT_READ | PROT_WRITE | PROT_EXEC,
  MAP_PRIVATE | MAP_ANONYMOUS,
  -1, 0);
 if (cod == MAP_FAILED)
 {
  printf ("mmap failed\n");
  exit(0);
 }
#endif
 lastword = NULL;
 freedic.p = dic;
 for (i=0; i<256; i++)
  lab[i] = 0;
#ifdef JNI
 cvmin = fopen ("/mnt/sdcard/cvmin.txt", "r");
#else
 cvmin = fopen ("cvmin.txt", "r");
#endif
 if (cvmin == NULL)
  cvmin = stdin;
 init_code ();
}




