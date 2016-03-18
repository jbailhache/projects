
#include "cvm.h"

#ifdef CVMDOS
#include "dos.h" 
#endif

pword getword (void);

extern char buf[1000];
void output (char *s);
#ifdef JNI
extern JNIEnv *genv;
#endif

#if 0
#include <stdio.h>
#include <stdlib.h>

typedef long instr;

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

extern instr cod[6000];

extern char awr[32];

typedef char chr;

struct word
{
 struct word *link;
 any code;
 any param;
 chr *pname;
 chr name[4];
};

typedef struct word *pword;

pword getword (void);

int f_scanhex (void);

#define code_mov_r0_im 0x1000F
#define code_q_mov_r0_imr0 0x101000F
#define code_mov_r1_im 0x1010F
#define code_q_mov_r1_imr0 0x101010F
#define code_mov_ra_im 0x10A0F
#define code_q_mov_ra_imr0 0x1010A0F
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

#endif



#define INSNAM(i,n) if (x==i) return n; else

char buf_instr_name[100];

const char *instr_name (instr x)
{
 if ((x & 0xFFFFF0F0) == 0x10000)
 {
  sprintf (buf_instr_name, "r%X=r%X", (x&0xF00)>>8, x&0xF);
  return buf_instr_name;
 }
 else
 INSNAM(code_mov_r0_im,"r0=")
 INSNAM(code_q_mov_r0_imr0,"code r0={r0}")
 INSNAM(code_mov_r1_im,"r1=")
 INSNAM(code_q_mov_r1_imr0,"code r1={r0}")
 INSNAM(code_mov_ra_im,"rA=")
 INSNAM(code_mov_ra_sva,"rA=sva")
 INSNAM(code_q_mov_ra_imr0,"code rA={r0}")
 INSNAM(code_mov_r1_r0,"r1=r0")
 INSNAM(code_q_mov_r1_r0,"code r1=r0")
 INSNAM(code_mov_r2_r0,"r2=r0")
 INSNAM(code_mov_r0_r2,"r0=r2")
 INSNAM(code_mov_r1_r2,"r1=r2")
 INSNAM(code_mov_ra_r0,"rA=r0")
 INSNAM(code_mov_rb_r0,"rB=r0")
 INSNAM(code_mov_rc_r0,"rC=r0")
 INSNAM(code_mov_r0_ra,"r0=rA")
 INSNAM(code_mov_r0_rb,"r0=rB")
 INSNAM(code_mov_r0_rc,"r0=rC")
 INSNAM(code_mov_ra_r1,"rA=r1")
 INSNAM(code_mov_rc_r1,"rC=r1")
 INSNAM(code_mov_rc_ra,"rC=rA")
 INSNAM(code_mov_r1_rc,"r1=rC")
 INSNAM(code_mov_r0_cont_ra,"r0=[rA]")
 INSNAM(code_mov_r0_byte_cont_ra,"r0=byte[rA]")
 INSNAM(code_mov_ra_cont_ra,"rA=[rA]")
 INSNAM(code_mov_cont_ra_r0,"[rA]=r0")
 INSNAM(code_mov_byte_cont_ra_r0,"byte[rA]=r0")
 INSNAM(code_mov_r0_cont_ra_plus_im,"r0=[rA+]")
 INSNAM(code_mov_cont_ra_plus_im_r0,"[rA+]=r0")
 INSNAM(code_mov_r0_cont_rb_inc,"r0=[rB++]")
 INSNAM(code_mov_cont_dec_rb_r0,"[--rB]=r0")
 INSNAM(code_mov_r1_cont_rb_inc,"r1=[rB++]")
 INSNAM(code_mov_ra_cont_rb_inc,"rA=[rB++]")
 INSNAM(code_mov_cont_dec_rb_r1,"[--rB]=r1")
 INSNAM(code_mov_cont_rc_inc_r0,"[rC++]=r0")
 INSNAM(code_mov_r0_retadr,"r0=retadr")
 INSNAM(code_mov_retadr_r0,"retadr=r0")
 INSNAM(code_mov_r0_lastword,"r0=lastword")
 INSNAM(code_mov_lastword_r0,"lastword=r0")
 INSNAM(code_mov_r0_freedic,"r0=freedic")
 INSNAM(code_mov_freedic_r0,"freedic=r0")
 INSNAM(code_add_r0_r1,"r0=r0+r1")
 INSNAM(code_sub_r0_r1,"r0=r0-r1")
 INSNAM(code_bp_depl,"bp")
 INSNAM(code_bz_depl,"bz")
 INSNAM(code_bp_ra,"bp rA")
 INSNAM(code_call_depl,"call")
 INSNAM(code_call_ra,"call rA")
 INSNAM(code_beginf,"beginf")
 INSNAM(code_endf,"endf")
 INSNAM(code_ret,"ret")
 INSNAM(code_ror_r0,"ror r0")
 INSNAM(code_asr_r0,"asr r0")
 INSNAM(code_and_r0_r1,"r0=r0&r1")
 INSNAM(code_xor_r0_r1,"r0=r0^r1")
 INSNAM(code_push_r0,"push r0")
 INSNAM(code_pop_r0,"pop r0")
 INSNAM(code_fillmem,"fillmem")
 INSNAM(code_callext,"callext")
 INSNAM(code_callext_ra,"callext rA")
 INSNAM(code_intbios,"intbios")
 INSNAM(code_getchar,"getchar")
 INSNAM(code_putchar,"putchar")
 INSNAM(code_scanhex,"scanhex")
 INSNAM(code_getword,"getword")
 INSNAM(code_getwordstr,"getwordstr")
 INSNAM(code_fopen,"fopen")
 INSNAM(code_fclose,"fclose")
 INSNAM(code_fgetc,"fgetc")
 INSNAM(code_fputc,"fputc")
 INSNAM(code_getprocadr,"getprocadr")
 INSNAM(code_setbradr,"setbradr")
 INSNAM(code_resetdraw,"resetdraw")
 INSNAM(code_draw,"draw")
 INSNAM(code_invalidate,"invalidate")
 INSNAM(code_exit,"exit")
 return "";
}



/* extern any r0, r1, r2, ra, rb, rc; */
/*
extern any reg[16];
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
#define rd reg[13]

#define STACKSIZE 1000
extern codeptr stack[STACKSIZE];
extern int sp;
*/

void dmpcodeadrlen (int adr, int len);

extern char mode;

void interp_debug (char mode, int param)
{
codeptr cp;
instr ins;
int depl;
any a;
char c;
char buf[100];
 /* printf ("sizeof(any)=%d\n",sizeof(any)); */
 cp = cod;
 sp = 0;
 ra.cp = cod;
 rb.cp = cod;
 r0.i = param;
 for (;;)
 {
  /*
  printf (" %X:",&mode);
  putchar(mode);
  */
  if (mode != 'r')
  {
  printf ("\n");
  printf ("r0=%08lX\n",r0.i);
  printf ("r1=%08lX\n",r1.i);
  printf ("r2=%08lX\n",r2.i);
  printf ("rA=%08lX [rA]=%08lX\n",ra.i,*(ra.p));
  printf ("rB=%08lX [rB]=%08lX\n",rb.i,*(rb.p));
  printf ("rC=%08lX\n",rc.i);
  }

  checkadr (cp);

  ins = *cp++;

  /* printf ("%s\n",instr_name(ins)); */

/*
  sprintf (buf, "%lX: %08lX %s %08lX", cp-1, ins, instr_name(ins), *cp); 
  trace (buf);

  sprintf (buf, "r0=%08lX r1=%08lX r2=%08lX rA=%08lX rB=%08lX rC=%08lX",
  r0.i, r1.i, r2.i, ra.i, rb.i, rc.i);
  trace (buf);
*/
  if (mode != 'r')
  {
  printf ("%lX: %08lX %s %08lX\n", cp-1, ins, instr_name(ins), *cp);
  printf ("debug> ");
  if (mode == 'd')
   gets(buf);
  else
   strcpy (buf, "");
  if (buf[0]=='q')
   return;
  else if (buf[0]=='d')
  {
   int adr,len;
   adr = 0;
   sscanf (buf+1,"%x %x",&adr,&len);
   printf ("adr=%X len=%X\n", adr, len);
   if (adr == 0)
    dmpcode();
   else
    dmpcodeadrlen(adr,len);
   /* continue; */
  }
  }
  /* printf ("%08X %08X\n", ins, *cp); */
  if (ins == code_mov_r0_im)
  {
    /* printf ("mov_r0_im: *cp=%lX\n", *(codeptr *)cp); */
    r0.ins = *cp++; 
    /*
    r0.cp = *(codeptr *)cp;
    cp++;
    */
  }
  else if (ins == code_mov_r1_im)
    r1.ins = *cp++;
  else if (ins == code_mov_ra_im)
    ra.ins = *cp++;
  else if (ins == code_mov_ra_sva)
    ra.pa = sva;
  else if (ins == code_q_mov_r0_imr0)
  {
    *(rc.p++) = code_mov_r0_im;
    *(rc.p++) = r0.ins;
  }
  else if (ins == code_q_mov_r1_imr0)
  {
    checkadr (rc.cp);
    *(rc.p++) = code_mov_r1_im;
    *(rc.p++) = r0.ins;
  }
  else if (ins == code_q_mov_ra_imr0)
  {
    checkadr (rc.cp);
    *(rc.p++) = code_mov_ra_im;
    *(rc.p++) = r0.ins;
  }
  else if ((ins & 0xFFFFF0F0) == code_mov_r_r)
  {
    int rd, rs;
    rd = (ins & 0xFF00) >> 8;
    rs = (ins & 0xFF);
/*
    sprintf (buf, "r%X=r%X", rd, rs);
    trace(buf);
*/
    reg[rd] = reg[rs];
  }
#if 0
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
#endif
  else if (ins == code_mov_r0_cont_ra)
  {
    checkadr (ra.cp);
    r0.i = *(ra.p);
  }
  else if (ins == code_mov_r0_byte_cont_ra)
  {
    checkadr (ra.cp);
    r0.i = *(ra.pchar);
  }
  else if (ins == code_mov_ra_cont_ra)
  {
    checkadr (ra.cp);
    ra.i = *(ra.p);
  }
  else if (ins == code_mov_cont_ra_r0)
  {
    checkadr (ra.cp);
    *(ra.p) = r0.i;
  }
  else if (ins == code_mov_byte_cont_ra_r0)
  {
    checkadr (ra.cp);
    *(ra.pchar) = r0.i;
  }
  else if (ins == code_mov_r0_cont_ra_plus_im)
  {
    /* r0.i = ra.p[((int)(*cp++))/4]; */
    /* trace ("r0=[rA+x]"); */
    r0.i = ra.p[((int)(*cp))/4];
    /* trace ("done"); */
    cp++;
    /* trace ("end"); */
  }
  else if (ins == code_mov_cont_ra_plus_im_r0)
  {
    /* ra.p[((int)(*cp++))/4] = r0.i; */
    ra.p[((int)(*cp))/4] = r0.i;
    cp++;
  }
  else if (ins == code_mov_r0_cont_rb_inc)
  {
   checkadr (rb.cp);
   r0.i = *(rb.p++);
  }
  else if (ins == code_mov_cont_dec_rb_r0)
  {
   checkadr (rb.cp-1);
   *(--rb.p) = r0.i;
  }
  else if (ins == code_mov_r1_cont_rb_inc)
  {
   r1.i = *(rb.p++);
   checkadr (rb.cp);
  }
  else if (ins == code_mov_ra_cont_rb_inc)
  {
   checkadr (rb.cp);
   ra.i = *(rb.p++);
  }
  else if (ins == code_mov_cont_dec_rb_r1)
  {
   checkadr (rb.cp-1);
   *(--rb.p) = r1.i;
  }
  else if (ins == code_mov_cont_rc_inc_r0)
  {
   checkadr (rc.cp);
   *(rc.p++) = r0.i;
  }
  else if (ins == code_mov_r0_retadr)
  {
   r0.cp = stack[sp-1];
  }
  else if (ins == code_mov_retadr_r0)
  {
   stack[sp-1] = r0.cp;
  }
  else if (ins == code_mov_r0_lastword)
  {
   r0.pw = lastword;
  }
  else if (ins == code_mov_lastword_r0)
  {
   lastword = r0.pw;
  }
  else if (ins == code_mov_r0_freedic)
  {
   r0 = freedic;
  }
  else if (ins == code_mov_freedic_r0)
  {
   freedic = r0;
  }
  else if (ins == code_add_r0_r1)
    r0.i = r0.i + r1.i;
  else if (ins == code_sub_r0_r1)
    r0.i = r0.i - r1.i;
  else if (ins == code_mul_r0_r1)
    r0.i = r0.i * r1.i;
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
  else if (ins == code_setbradr)
  {
   /* rA = adresse de l'instruction de saut bp
      r0 = adresse du saut */
   int depl;
   depl = r0.cp - ra.cp - 2;
   checkadr (ra.cp+1);
   ra.cp[1] = depl;
   /* printf ("setbradr: rA=%X r0=%X depl=%X\n", ra.cp, r0.cp, depl); */
  }
  else if (ins == code_call_depl)
  {
    /* trace ("call depl"); */
    if (sp>=STACKSIZE-1)
    {
     printf("\nstack overflow\n");
     trace ("stack overflow");
     exit(0);
     break;
    }
    /* trace("stack ok"); */
    depl = (int) *cp++;
    /* trace ("depl ok"); */
    stack[sp++] = cp;
    /* trace ("cp pushed"); */
    cp += depl;
    /* trace ("end call depl"); */
  }
  else if (ins == code_call_ra)
  {
    if (sp >= STACKSIZE)
    {
     printf ("\nstack overflow\n");
     trace ("stack overflow");
     /* exit(0); */
     return;
    }
    stack[sp++] = cp;
    cp = ra.cp;
  }
  else if (ins == code_push_r0)
  {
    if (sp >= STACKSIZE)
    {
     printf ("\nstack overflow\n");
     trace ("stack overflow");
     /* exit(0); */
     return;
    }
    stack[sp++] = r0.cp;
  }
  else if (ins == code_pop_r0)
  {
    if (sp <= 0)
    {
     printf ("\nstack underflow\n");
     trace ("stack underflow");
     /* exit(0); */
     return;
    }
    r0.cp = stack[--sp];
  }
  else if (ins==code_beginf);
  else if (ins == code_ret || ins==code_endf)
  {
    if (sp <= 0)
    {
     printf ("\nstack underflow\n");
     trace ("stack underflow");
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
    r0.i = a.extf (r0.i, r1.i, r2.i, r3.i, r4.i, r5.i, r6.i, r7.i);
  }
  else if (ins == code_callext_ra)
  {
   r0.i = ra.extf (r0.i, r1.i, r2.i,  r3.i, r4.i, r5.i, r6.i, r7.i);
  }
  else if (ins == code_intbios)
  {
#ifdef CVMDOS
   any intnum;
   union REGS regs;
   intnum.ins = *cp++;
   regs.x.ax = r0.i;
   regs.x.bx = rb.i;
   regs.x.cx = r2.i;
   regs.x.dx = r1.i;
   /* regs.x.bp = r9.i; */
   regs.x.si = ra.i;
   regs.x.di = rc.i;
   int86 (intnum.i, &regs, &regs);
   r0.i = regs.x.ax;
   rb.i = regs.x.bx;
   r2.i = regs.x.cx;
   r1.i = regs.x.dx;
   /* r9.i = regs.x.bp; */
   ra.i = regs.x.si;
   rc.i = regs.x.di;
#endif
  }
  else if (ins == code_getchar)
    r0.i = getchr();
  else if (ins == code_putchar)
    /* putchar (r0.i);*/
  {
   sprintf (buf, "%c", r0.i);
   output (buf);
  }
  else if (ins == code_getword)
  {
    ra.pw = getword();
    r0.i = 0;
    sscanf (awr, "%x", &r0.i);
  }
  else if (ins == code_getwordstr)
  {
    ra.pw = getwordstr (r0.pchr);
    r0.i = 0;
    sscanf (awr, "%x", &r0.i);
  }
  else if (ins == code_scanhex)
    r0.i = f_scanhex ();
  else if (ins == code_printhex)
    f_printhex (r0.i);
  else if (ins == code_printdec)
  {
    /* trace ("before f_printdec"); */
    f_printdec (r0.i);
    /* trace ("after f_printdec"); */
  }
  else if (ins == code_sscandec)
    r0.i = f_sscandec (r0.pchar);

  else if (ins == code_fopen)
  {
  /*
   switch(r1.i & 3)
   {
    case 0:
     r0.fd = fopen (r0.pchar, "r");
     break;
    case 1:
     r0.fd = fopen (r0.pchar, "w");
     break;
    case 2:
     r0.fd = fopen (r0.pchar, "rw");
     break;
   }
   */
   r0.fd = f_fopen (r0.i, r1.pchar);
  }
  else if (ins == code_fclose)
   r0.i = fclose (r0.fd);
  else if (ins == code_fgetc)
   r0.i = fgetc (r0.fd);
  else if (ins == code_fputc)
   r0.i = fputc (r1.i, r0.fd);

#ifdef SOCKET
  else if (ins == code_socket)
   r0.i = socket (r0.i, r1.i, r2.i);
  else if (ins == code_closesocket)
   r0.i = close (r0.i);
  else if (ins == code_listen)
   r0.i = listen (r0.i, r1.i);
  else if (ins == code_accept)
   r0.i = accept (r0.i, r1.pvoid, r2.pint);
  else if (ins == code_bind)
   r0.i = bind (r0.i,r1.pvoid, r2.i);
  else if (ins == code_connect)
   r0.i = connect (r0.i, r1.pvoid, r2.i);
  else if (ins == code_recv)
   r0.i = recv (r0.i, ra.pchar, r1.i, r2.i);
  else if (ins == code_send)
   r0.i = send (r0.i, ra.pchar, r1.i, r2.i);
#endif

#ifdef JNI
  else if (ins == code_findclass)
   r0.cls = (*genv)->FindClass (genv, r0.pchar);
  else if (ins == code_getmethodid)
   r0.mid = (*genv)->GetMethodID (genv, r0.cls, r1.pchar, r2.pchar);
  else if (ins == code_callmethoda)
   r0.i = CallMethodA (genv, r0.obj, r1.mid, ra.pjvalue, r2.i);
  else if (ins == code_getstringutfchars)
   r0.pchar = (*genv)->GetStringUTFChars (genv, r0.js, r1.i);
  else if (ins == code_newstringutf)
   r0.js = (*genv)->NewStringUTF (genv, r0.pchar);

  else if (ins == code_resetdraw)
  {
   trace ("reset_draw ...");
   reset_draw();
  }
  else if (ins == code_invalidate)
  {
   trace ("invalidate ...");
   invalidate_view();
  }
  else if (ins == code_draw)
  {
   trace ("draw ...");
   draw (r0.i, r1.i, ra.pint);
  }
#endif

  else if (ins == code_getprocadr)
  {
#ifdef PPC
    r0.intf = getprocadr (r0.pwchar, r1.pwchar);
#endif
#ifdef DEVCPP
    r0.intf = getprocadr (r0.pchar, r1.pchar);
#endif
#ifdef LINUX
    r0.intf = getprocadr (r0.pchar, r1.pchar);
#endif
  }
  else if (ins == code_fillmem)
  {
   int n, i;
   n = (int)(*cp++);
   for (i=0; i<n; i++)
    *(rc.cp++) = *cp++;
  }
  else if (ins == code_dumpcode)
   dmpcode();
  else if (ins == code_initcvm)
   initcvm();
  else if (ins == code_brkdbg)
   brkdbg(0);
  else if (ins == code_exit)
   /* exit (r0.i); */ 
   return ;
  else
    printf ("Instruction %X not implemented\n", ins);

 }

}

void interp (int param)
{
 interp_debug ('r',param);
}

void debug (void)
{
 interp_debug (mode,1);
}


