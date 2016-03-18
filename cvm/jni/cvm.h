
/* #define PPC */
/* #define INTERP */  /* This definition must be uncommented to compile with Dev-C++ */
/* #define COMPARM */
/* #define COMPX86 */
/* #define DEVCPP */  /* This definition must be uncommented to compile with Dev-C++ */

/* add this for Android version  */
/*
#define INTERP 
#define JNI 
#define SOCKET
*/

#ifndef PPC
#include <stdio.h>
#endif

#ifdef PPC
#include <windows.h>
#include <windowsx.h>
#endif

#include <stdlib.h>
#include <string.h>

#ifdef JNI
#include <jni.h>
#endif

#ifdef SOCKET
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <unistd.h>
#endif

#ifdef LINUXCOMP
#include <sys/mman.h>
#endif

#ifndef CVMDOS
#define far
#endif

#include "target.h"

int brkdbg(int);

void printasm (char *s, unsigned int x, unsigned int adr);
void debug (void);

#define NLABELS 0x100
#define LEN 0x20

struct labels
{
	char name[LEN];
	unsigned long value;
} ;

#ifdef GBLVARS
struct labels labels[NLABELS];
#else
extern struct labels labels[NLABELS];
#endif


typedef unsigned char chr;
typedef char octet;

#if 0

#ifdef INTERP
typedef long instr;
#endif

#ifdef COMPARM
typedef int instr;
#endif

#ifdef COMPX86
typedef unsigned char instr;
#endif

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
 long far *p;
 int far *pint;
 codeptr cp;
 codefn f;
 void (*f1) (int);
 void (far *vf) (void);
 int (far *intf)();
 int (far *extf) (int, int, int, int, int, int, int, int);
 struct word far *pw;
 union any far *pa;
 FILE *fd;
 char far *pchar;
 chr far *pchr;
#if (defined(PPC) || defined(DEVCPP))
 wchar_t far *pwchar;
#endif
 void far *pvoid;
#ifdef JNI
 jclass cls;
 jmethodID mid;
 jobject obj;
 jvalue *pjvalue;
 jstring js;

#endif
} any;

#ifdef COMPARM
#define CODESIZE 16000
#else
#define CODESIZE 8000
#endif

#define NLAB 256

#ifdef GBLVARS
#ifdef LINUXCOMP
instr *cod;
#else
instr cod[CODESIZE];
#endif
codeptr lab[NLAB];
int nlab = 0;
#else
#ifdef LINUXCOMP
extern instr *cod;
#else
extern instr cod[CODESIZE];
#endif
extern codeptr lab[NLAB];
extern int nlab;
#endif

struct label
{
	char name[LEN];
	any value;
};

#ifdef GBLVARS
struct label label[NLABELS];
#else
extern struct label label[NLABELS];
#endif

/*
struct word
{
 struct word far *link;
 any code;
 any param;
 chr far *pname;
 chr name[4];
};
*/

struct word 
{
 any alink;
 any code;
 any param;
 long flags;
 any apname;
 chr name[4];
};

#define link alink.pw
#define pname apname.pchr

typedef struct word far *pword;

/*
#ifdef GBLVARS
pword lastword = NULL;
#else
extern pword lastword;
#endif
*/

#define DICSIZE 1000

#ifdef GBLVARS
long dic[DICSIZE];

any freedic;
any freespace;

pword gpw;
int gwri;
#else
extern int dic[DICSIZE];

extern any freedic;
extern any freespace;

extern pword gpw;
extern int gwri;
#endif

#define NSVA 16
#ifdef GBLVARS
any sva[NSVA];
#else
extern any sva[NSVA];
#endif


#define lastword (sva[1].pw)
/*
#define freedic (sva[2])
#define freespace (sva[3])
*/
/*
codeptr c_mov_ra_im (codeptr cp, int im, char *l);
codeptr c_mov_r0_cont_ra (codeptr cp);
codeptr c_mov_ra_cont_ra (codeptr cp);
*/

#ifdef JNI
void reset_draw (void);
void draw (int op, int color, int *p);
#endif

chr getchr1(void);

#ifdef GBLVARS
FILE *cvmin = NULL;
chr (*pgetchr) (void) = getchr1;
#define getchr (*pgetchr)
#else
extern FILE *cvmin;
extern chr (*pgetchr) (void) ;
#define getchr (*pgetchr)
#endif

#define WORDSIZE 32

#ifdef GBLVARS
chr cr;
chr wr[WORDSIZE];
char awr[WORDSIZE];
#else
extern chr cr;
extern chr wr[WORDSIZE];
extern char awr[WORDSIZE];
#endif


#define code_mov_r0_im 0x21000F
#define code_q_mov_r0_imr0 0x101000F
#define code_mov_r1_im 0x1010F
#define code_q_mov_r1_imr0 0x101010F
#define code_mov_ra_im 0x210A0F
#define code_mov_ra_sva 0x310A0F
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
#define code_mov_r0_byte_cont_ra 0x1002A
#define code_mov_ra_cont_ra 0x10A1A
#define code_mov_cont_ra_r0 0x11A00
#define code_mov_byte_cont_ra_r0 0x12A00
#define code_mov_r0_cont_ra_plus_im 0x1009A
#define code_mov_cont_ra_plus_im_r0 0x19A00
#define code_mov_r0_cont_rb_inc 0x1005B
#define code_mov_cont_dec_rb_r0 0x13B00
#define code_mov_r1_cont_rb_inc 0x1015B
#define code_mov_ra_cont_rb_inc 0x10A5B
#define code_mov_cont_dec_rb_r1 0x13B01
#define code_mov_cont_rc_inc_r0 0x15C00
#define code_mov_r0_retadr 0x1000D
#define code_mov_retadr_r0 0x10D00
#define code_mov_r0_lastword 0x100F0
#define code_mov_lastword_r0 0x1F000
#define code_mov_r0_freedic 0x100F1
#define code_mov_freedic_r0 0x1F100
#define code_add_r0_r1 0x20001
#define code_sub_r0_r1 0x30001
#define code_mul_r0_r1 0x40001
#define code_bp_depl 0xC2FFF
#define code_bz_depl 0xC3FFF
#define code_bp_ra 0xC0AFF
#define code_bz_ra 0xC0BFF
#define code_call_depl 0xD2FFF
#define code_call_ra 0xD0AFF
#define code_beginf 0xE0001
#define code_endf 0xE0002
#define code_ret 0xEFFFF
#define code_ror_r0 0x600FF
#define code_asr_r0 0x700FF
#define code_and_r0_r1 0x80001
#define code_xor_r0_r1 0x90001
#define code_push_r0 0xA0000
#define code_pop_r0 0xB0000
#define code_fillmem 0xE0000
#define code_callext 0xFFF0F
#define code_callext_ra 0xFFF0A
#define code_intbios 0x17FF0F
#define code_getchar 0x1000FF
#define code_putchar 0x11FF00
#define code_scanhex 0x1200FF
#define code_printhex 0x15FF00
#define code_printdec 0x1BFF00
#define code_getword 0x1300FF
#define code_getwordstr 0x1300FE
#define code_fopen 0x310001
#define code_fclose 0x320000
#define code_fgetc 0x330000
#define code_fputc 0x340001
#define code_setbradr 0x140000
#define code_dumpcode 0x16FFFF
#define code_getprocadr 0x180001
#define code_initcvm 0x19FFFF
#define code_sscandec 0x1A00FF
#define code_exit 0xFFFFFF

#ifdef SOCKET
#define code_socket 0x400000
#define code_closesocket 0x410000
#define code_listen 0x420000
#define code_accept 0x430000
#define code_bind 0x440000
#define code_connect 0x450000
#define code_recv 0x460000
#define code_send 0x470000
#endif

#define code_findclass 0x510000
#define code_getmethodid 0x520000
#define code_callmethoda 0x530000
#define code_getstringutfchars 0x540000
#define code_newstringutf 0x550000

#define code_resetdraw 0x610000
#define code_draw 0x620000
#define code_invalidate 0x630000
#define code_brkdbg 0x700000 


#ifdef GBLVARS
FILE *f_tasm = NULL;
FILE *f_asmi = NULL;
FILE *f_asml = NULL;
FILE *f_x86 = NULL;
char last_label[200];
#else
extern FILE *f_tasm ;
extern FILE *f_asmi ;
extern FILE *f_asml ;
extern FILE *f_x86 ;
extern char last_label[200];
#endif

/* char last_label; */

#define STACKSIZE 1000

#ifdef GBLVARS
any reg[16];

codeptr stack[STACKSIZE];
int sp;

#else

extern any reg[16];

extern codeptr stack[STACKSIZE];
extern int sp;

#endif

#ifdef GBLVARS
int gnw = 0;
#else
extern int gnw;
#endif

#define r0 reg[0]
#define r1 reg[1]
#define r2 reg[2]
#define r3 reg[3]
#define r4 reg[4]
#define r5 reg[5]
#define r6 reg[6]
#define r7 reg[7]
#define r8 reg[8]
#define r9 reg[9]
#define ra reg[10]
#define rb reg[11]
#define rc reg[12]
/*#define rd reg[13]*/

#define STACKSIZE 1000

int trace (char *s);

void checkadr (instr *adr);

void init_dic (void);
chr getchr1 ();
void putchr (chr c);
void printdec (int i);
void printhex (int i);
chr readcarac (void);
int isblnk (chr c);
int iswordcarac (chr c);
void readto (char delim, char *ptr);
void readword (void);
int slen (chr *s);
int scmp (chr *s1, chr *s2);
chr * scpy (chr *s1, chr *s2);
codeptr compile_pushint (codeptr cp, int x);
pword findword (chr *name);
pword createword (chr *name);
pword getwordstr (chr *name);
pword getword (void);
int f_getchar (void);
void f_putchar (int c);
void f_print (int x);
long f_scanhex (void);
void interp (int param);
int isdgt (char c);
codeptr compile_op (codeptr cp, char *op, int nargs, long *iargs, char largs[8][200], char *s);
long value_of_label (char *name);
codeptr compile_string (codeptr cp, char *s);
codeptr compile_file (codeptr cp, const char *fn,
 const char *fn_tasm, const char *fn_asmi, const char *fn_asml, const char *fn_x86);
void init (void);

#ifdef JNI
void reset_draw (void);
void draw (int, int, int *);
void invalidate_view (void);
#endif

codeptr c_push_r0 (codeptr cp);
codeptr c_pop_r0 (codeptr cp);
codeptr c_push_r1 (codeptr cp);
codeptr c_pop_r1 (codeptr cp);
codeptr c_pop_r2 (codeptr cp);
void setbradr (instr *from, instr *to);
codeptr compile_call0 (codeptr cp, int (*f)());
codeptr compile_call (codeptr cp, int (*f)(), int regs, int res);
codeptr c_getchar (codeptr cp);
codeptr c_putchar (codeptr cp);
codeptr c_getword (codeptr cp);
codeptr c_getwordstr (codeptr cp);
codeptr c_scanhex (codeptr cp);
codeptr c_fopen (codeptr cp);
codeptr c_fclose (codeptr cp);
codeptr c_fgetc (codeptr cp);
codeptr c_fputc (codeptr cp);
codeptr c_mov_r0_im (codeptr cp, long im, char *l);
codeptr c_mov_r1_im (codeptr cp, long im, char *l);
codeptr c_mov_ra_im (codeptr cp, long im, char *l);
codeptr c_mov_ra_sva (codeptr cp);
codeptr c_q_mov_r0_imr0 (codeptr cp);
codeptr c_q_mov_r1_imr0 (codeptr cp);
codeptr c_q_mov_ra_imr0 (codeptr cp);
codeptr c_mov_r_r (codeptr cp, int rd, int rs);
codeptr c_q_mov_r1_r0 (codeptr cp);
codeptr c_mov_r0_cont_ra (codeptr cp);
codeptr c_mov_r0_byte_cont_ra (codeptr cp);
codeptr c_mov_ra_cont_ra (codeptr cp);
codeptr c_mov_cont_ra_r0 (codeptr cp);
codeptr c_mov_byte_cont_ra_r0 (codeptr cp);
codeptr c_mov_r0_cont_ra_plus_im (codeptr cp, int im);
codeptr c_mov_cont_ra_plus_im_r0 (codeptr cp, int im);
codeptr c_mov_r0_cont_rb_inc (codeptr cp);
codeptr c_mov_cont_dec_rb_r0 (codeptr cp);
codeptr c_mov_r1_cont_rb_inc (codeptr cp);
codeptr c_mov_ra_cont_rb_inc (codeptr cp);
codeptr c_mov_cont_dec_rb_r1 (codeptr cp);
codeptr c_mov_cont_rc_inc_r0 (codeptr cp);
codeptr c_mov_r0_retadr (codeptr cp);
codeptr c_mov_retadr_r0 (codeptr cp);
codeptr c_mov_r0_lastword (codeptr cp);
codeptr c_mov_lastword_r0 (codeptr cp);
codeptr c_mov_r0_freedic (codeptr cp);
codeptr c_mov_freedic_r0 (codeptr cp);
codeptr c_add_r0_r1 (codeptr cp);
codeptr c_sub_r0_r1 (codeptr cp);
codeptr c_mul_r0_r1 (codeptr cp);
codeptr c_bp_depl (codeptr cp, int depl);
codeptr c_bz_depl (codeptr cp, int depl);
codeptr c_setbradr (codeptr cp);
codeptr c_bp_ra (codeptr cp);
codeptr c_bz_ra (codeptr cp);
codeptr c_call_depl (codeptr cp, int depl);
codeptr c_call_ra (codeptr cp);
codeptr c_beginf (codeptr cp);
codeptr c_endf (codeptr cp);
codeptr c_ret (codeptr cp);
codeptr c_ror_r0 (codeptr cp);
codeptr c_asr_r0 (codeptr cp);
codeptr c_and_r0_r1 (codeptr cp);
codeptr c_xor_r0_r1 (codeptr cp);
int f_exit (void);
codeptr c_exit (codeptr cp);
codeptr c_code (codeptr cp);
codeptr c_endcode (codeptr cp);
codeptr c_dumpcode(codeptr cp);
codeptr c_call_dummy(codeptr cp);
codeptr c_dummyprint(codeptr cp);
codeptr c_getprocadr (codeptr cp);
codeptr c_initcvm (codeptr cp);
codeptr c_sscandec (codeptr cp);
codeptr c_printdec (codeptr cp);
codeptr c_intbios (codeptr cp, int n);
codeptr c_callext_ra (codeptr cp);

#ifdef SOCKET
codeptr c_socket (codeptr cp);
codeptr c_closesocket (codeptr cp);
codeptr c_listen (codeptr cp);
codeptr c_accept (codeptr cp);
codeptr c_bind (codeptr cp);
codeptr c_connect (codeptr cp);
codeptr c_recv (codeptr cp);
codeptr c_send (codeptr cp);
#endif

#ifdef JNI

int CallMethodA (JNIEnv *env, jobject obj, jmethodID mid, jvalue *args, int type);

codeptr c_findclass (codeptr cp);
codeptr c_getmethodid (codeptr cp);
codeptr c_callmethoda (codeptr cp);
codeptr c_getstringutfchars (codeptr cp);
codeptr c_newstringutf (codeptr cp);

#endif

codeptr c_resetdraw (codeptr cp);
codeptr c_draw (codeptr cp);
codeptr c_invalidate (codeptr cp);

codeptr c_brkdbg (codeptr cp);

void init_code (void);

const char *instr_name (instr x);

void dmpcode (void);

codeptr c_printhex (codeptr cp);
void f_printhex (int x);

typedef int (*ft)();

#ifdef PPC
ft getprocadr (wchar_t *mn, wchar_t *fn);
#else
#ifdef DEVCPP
ft getprocadr (char *mn, char *fn);
#else
ft getprocadr (char *mn, char *fn);
#endif
#endif

FILE * f_fopen (int mode, char *fn);

void initcvm(void);

void f_printdec (int);
int f_sscandec (char *);

void f_dummyprint(void);


void clearcache(void);










