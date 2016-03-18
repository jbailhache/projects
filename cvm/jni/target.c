
#ifdef PPC
#include <windows.h>
#include <windowsx.h>
#endif

#include "cvm.h"

#ifdef DEVCPP
#include <windows.h>
#include <windowsx.h>
#endif

#ifdef LINUX
#include <dlfcn.h>
#endif

extern char buf[1000];
void output (char *s);

void asm_call_ext (char *fn)
{
 trace ("asm_call_ext");
 /* fprintf (f_tasm, " push bp\n lea bp, _%s\n call bp\n pop bp\n", fn); */
 /* fprintf (f_tasm, " lea bp, _%s\n call bp\n", fn); */
 fprintf (f_tasm, " mov [word ptr sdx],dx\n");
 fprintf (f_tasm, " mov [word ptr scx],cx\n");
 fprintf (f_tasm, " mov [word ptr ssi],si\n");
 fprintf (f_tasm, " mov [word ptr sbx],bx\n");
 fprintf (f_tasm, " mov [word ptr sdi],di\n");
 fprintf (f_tasm, " lea bp,_%s\n", fn);
 fprintf (f_tasm, " call bp\n");
 fprintf (f_tasm, " mov dx,[word ptr sdx]\n");
 fprintf (f_tasm, " mov cx,[word ptr scx]\n");
 fprintf (f_tasm, " mov si,[word ptr ssi]\n");
 fprintf (f_tasm, " mov bx,[word ptr sbx]\n");
 fprintf (f_tasm, " mov di,[word ptr sdi]\n");
}

void asm_call_dummy (void)
{
 /* fprintf (f_tasm, " push bp\n lea bp, _%s\n call bp\n pop bp\n", fn); */
 /* fprintf (f_tasm, " lea bp, _%s\n call bp\n", fn); */
 fprintf (f_tasm, " mov [word ptr sdx],dx\n");
 fprintf (f_tasm, " mov [word ptr scx],cx\n");
 fprintf (f_tasm, " mov [word ptr ssi],si\n");
 fprintf (f_tasm, " mov [word ptr sbx],bx\n");
 fprintf (f_tasm, " mov [word ptr sdi],di\n");
/*
 fprintf (f_tasm, " lea bp,_%s\n", fn);
 fprintf (f_tasm, " call bp\n");
*/
 fprintf (f_tasm, " mov dx,[word ptr sdx]\n");
 fprintf (f_tasm, " mov cx,[word ptr scx]\n");
 fprintf (f_tasm, " mov si,[word ptr ssi]\n");
 fprintf (f_tasm, " mov bx,[word ptr sbx]\n");
 fprintf (f_tasm, " mov di,[word ptr sdi]\n");
}

codeptr c_brkdbg (codeptr cp)
{
 cp=compile_call(cp,(int(*)())brkdbg,0,0);
 return cp;
}

codeptr c_mov_r0_retadr (codeptr cp)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " pop ax\n push ax\n");
 if (f_asmi != NULL)
  fprintf (f_asmi, " pop %%ax\n push %%ax\n");
 if (f_asml != NULL)
  fprintf (f_asml, " pop %%ax\n push %%ax\n");
 if (f_x86 != NULL)
  fprintf (f_x86, " .byte 0x58, 0x50\n");
#ifdef INTERP
 *cp++ = code_mov_r0_retadr;
#endif
#ifdef COMPARM
 *cp++ = 0xE1A0A00E;
#endif
#ifdef COMPX86
 *cp++ = 0x58;
 *cp++ = 0x50;
#endif
}

codeptr c_mov_retadr_r0 (codeptr cp)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " inc sp\n inc sp\n push ax\n");
 if (f_asmi != NULL)
  fprintf (f_asmi, " inc %%sp\n inc %%sp\n push %%ax\n");
 if (f_asml != NULL)
  fprintf (f_asml, " inc %%sp\n inc %%sp\n push %%ax\n");
 if (f_x86 != NULL)
  fprintf (f_x86, " .byte 0x44, 0x44, 0x50\n");
#ifdef INTERP
 *cp++ = code_mov_retadr_r0;
#endif
#ifdef COMPARM
 *cp++ = 0xE1A0E00A;
#endif
#ifdef COMPX86
 *cp++ = 0x44;
 *cp++ = 0x44;
 *cp++ = 0x50;
#endif
}

pword f_mov_r0_lastword (void)
{
 return lastword;
}

codeptr c_mov_r0_lastword (codeptr cp)
{
#ifdef INTERP
 *cp++ = code_mov_r0_lastword;
#else
 cp = compile_call0 (cp, ((int(*)()) f_mov_r0_lastword));
#endif
}

any f_mov_lastword_r0 (any r0)
{
 lastword = r0.pw;
 return r0;
}

codeptr c_mov_lastword_r0 (codeptr cp)
{
#ifdef INTERP
 *cp++ = code_mov_lastword_r0;
#else
 cp = compile_call0 (cp, ((int(*)()) f_mov_lastword_r0));
#endif
}

any f_mov_r0_freedic (void)
{
 return freedic;
}

codeptr c_mov_r0_freedic (codeptr cp)
{
#ifdef INTERP
 *cp++ = code_mov_r0_freedic;
#else
 cp = compile_call0 (cp, ((int(*)()) f_mov_r0_freedic)); 
#endif
}

any f_mov_freedic_r0 (any r0)
{
 freedic = r0;
 return r0;
}

codeptr c_mov_freedic_r0 (codeptr cp)
{
#ifdef INTERP
 *cp++ = code_mov_freedic_r0;
#else
 cp = compile_call0 (cp, ((int(*)()) f_mov_freedic_r0));
#endif
}

codeptr c_push_r0 (codeptr cp)
{
 trace ("c_push_r0");
 if (f_tasm != NULL)
  fprintf (f_tasm, " push ax\n");
 if (f_asmi != NULL)
  fprintf (f_asmi, " push %%ax\n");
 if (f_asml != NULL)
  fprintf (f_asml, " push %%ax\n");
 if (f_x86 != NULL)
  fprintf (f_x86, " .byte 0x50\n");
#ifdef INTERP
 *cp++ = code_push_r0;
#endif
#ifdef COMPARM

#endif
#ifdef COMPX86
 *cp++ = 0x50;
#endif
 return cp;
}

codeptr c_pop_r0 (codeptr cp)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " pop ax\n");
 if (f_asmi != NULL)
  fprintf (f_asmi, " pop %%ax\n");
 if (f_asml != NULL)
  fprintf (f_asml, " pop %%ax\n");
 if (f_x86 != NULL)
  fprintf (f_x86, " .byte 0x58\n");
#ifdef INTERP
 *cp++ = code_pop_r0;
#endif
#ifdef COMPARM

#endif
#ifdef COMPX86
 *cp++ = 0x58;
#endif
 return cp;
}

codeptr c_push_r1 (codeptr cp)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " push bx\n");
 if (f_asmi != NULL)
  fprintf (f_asmi, " push %%bx\n");
 if (f_asml != NULL)
  fprintf (f_asml, " push %%bx\n");
 if (f_x86 != NULL)
  fprintf (f_x86, " .byte 0x53\n");
#ifdef COMPARM

#endif
#ifdef COMPX86
 *cp++ = 0x53;
#endif
 return cp;
}

codeptr c_pop_r1 (codeptr cp)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " pop bx\n");
 if (f_asmi != NULL)
  fprintf (f_asmi, " pop %%bx\n");
 if (f_asml != NULL)
  fprintf (f_asml, " pop %%bx\n");
 if (f_x86 != NULL)
  fprintf (f_x86, " .byte 0x5B\n");
#ifdef COMPARM

#endif
#ifdef COMPX86
 *cp++ = 0x5B;
#endif
 return cp;
}

codeptr c_pop_r2 (codeptr cp)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " pop cx\n");
 if (f_asmi != NULL)
  fprintf (f_asmi, " pop %%cx\n");
 if (f_asml != NULL)
  fprintf (f_asml, " pop %%cx\n");
 if (f_x86 != NULL)
  fprintf (f_x86, " .byte 0x59\n");
#ifdef COMPARM

#endif
#ifdef COMPX86
 *cp++ = 0x59;
#endif
 return cp;
}

#ifdef INTERP

void setbradr (instr *from, instr *to)
{
 int depl;
 checkadr(from);
 depl = to - (from+2);
 from[1] = depl;
}

codeptr compile_call0 (codeptr cp, int (*f)())
{
 *cp++ = code_callext;
 *cp++ = (instr)f;
 return cp;
}

codeptr compile_call (codeptr cp, int (*f)(), int regs, int res)
{
 compile_call0 (cp, f);
}

#endif

#ifdef COMPARM

void setbradr (instr *from, instr *to)
{
 int ofs;
 ofs = to - (from + 3);
#ifdef TRACE
 printf("from=%X to=%X ofs=%X from[1]=%X\n",
  from,to,ofs,from[1]);
#endif
 /* *from |= ofs; */
 /* *from = (*from & 0xFF000000) | (ofs & 0xFFFFFF); */
 from[1] = (from[1] & 0xFF000000) | (ofs & 0xFFFFFF);
#ifdef TRACE
 printf("from[1]=%X\n",from[1]);
#endif
}

instr instr_call (instr *ptrcode, int (*f)())
{
	union
	{
		int (*f)();
		int i;
	} uf;
	union
	{
		instr *pc;
		int i;
	} upc;
	unsigned int ofs;
	uf.f = f;
	upc.pc = ptrcode;
	ofs = (uf.i-(upc.i+8))/4;
	ofs &= 0xFFFFFF;
	return 0xEB000000 | ofs;
}

instr * compile_call (instr *ptrcode, int (*f)(), int regs, int res)
{
	any a;

	if (regs)
		*ptrcode++ = 0xE8BB0000 | regs;

	/*
	*ptrcode = instr_call (ptrcode, f); 
	ptrcode++;
	*/
	
	/* test : */

	a.intf = f;
#if 0
	*ptrcode++ = 0xE92D1C06; /* PUSH RD 1C02 */
	*ptrcode++ = 0xE28FE004; /* RE=RF+4 */
	*ptrcode++ = 0xE51FF004; /* RF=[RF-4] */
	*ptrcode++ = a.ins;
	*ptrcode++ = 0xE8BD1C06; /* POP RD 1C02 */
#endif

	*ptrcode++ = 0xE58F1018; /* [RF+18] = R1 */
	*ptrcode++ = 0xE58F2018; /* [RF+18] = R2 */
	*ptrcode++ = 0xE58FA018; /* [RF+18] = RA */
	*ptrcode++ = 0xE58FB018; /* [RF+18] = RB */
	*ptrcode++ = 0xE58FC018; /* [RF+18] = RC */
	*ptrcode++ = 0xE28FE018; /* RE = RF+18 */
	*ptrcode++ = 0xE51FF004; /* RF = [RF-4] */
	*ptrcode++ = a.ins;
	*ptrcode++ = (instr)0;
	*ptrcode++ = (instr)0;
	*ptrcode++ = (instr)0;
	*ptrcode++ = (instr)0;
	*ptrcode++ = (instr)0;
	*ptrcode++ = 0xE51F101C; /* R1 = [RF-1C] */
	*ptrcode++ = 0xE51F201C; /* R2 = [RF-1C] */
	*ptrcode++ = 0xE51FA01C; /* RA = [RF-1C] */
	*ptrcode++ = 0xE51FB01C; /* RB = [RF-1C] */
	*ptrcode++ = 0xE51FC01C; /* RC = [RF-1C] */

	if (res)
		*ptrcode++ = 0xE92B0000 | res;
	return ptrcode;
}

instr * compile_call_dummy (instr *ptrcode)
{
	any a;

		/*
	*ptrcode = instr_call (ptrcode, f); 
	ptrcode++;
	*/
	
	/* test : */

	/* a.intf = f;*/
#if 0
	*ptrcode++ = 0xE92D1C06; /* PUSH RD 1C02 */
	*ptrcode++ = 0xE28FE004; /* RE=RF+4 */
	*ptrcode++ = 0xE51FF004; /* RF=[RF-4] */
	*ptrcode++ = a.ins;
	*ptrcode++ = 0xE8BD1C06; /* POP RD 1C02 */
#endif

	*ptrcode++ = 0xE58F1018; /* [RF+18] = R1 */
	*ptrcode++ = 0xE58F2018; /* [RF+18] = R2 */
	*ptrcode++ = 0xE58FA018; /* [RF+18] = RA */
	*ptrcode++ = 0xE58FB018; /* [RF+18] = RB */
	*ptrcode++ = 0xE58FC018; /* [RF+18] = RC */
	/* *ptrcode++ = 0xE28FE018; */ /* RE = RF+18 */
	*ptrcode++ = 0xE28FF018; /* RF = RF+18 */
	/* *ptrcode++ = 0xE51FF004; */ /* RF = [RF-4] */
	/* *ptrcode++ = a.ins; */
	*ptrcode++ = (instr)0;
	*ptrcode++ = (instr)0;

	*ptrcode++ = (instr)0;
	*ptrcode++ = (instr)0;
	*ptrcode++ = (instr)0;
	*ptrcode++ = (instr)0;
	*ptrcode++ = (instr)0;
	*ptrcode++ = 0xE51F101C; /* R1 = [RF-1C] */
	*ptrcode++ = 0xE51F201C; /* R2 = [RF-1C] */
	*ptrcode++ = 0xE51FA01C; /* RA = [RF-1C] */
	*ptrcode++ = 0xE51FB01C; /* RB = [RF-1C] */
	*ptrcode++ = 0xE51FC01C; /* RC = [RF-1C] */

	
		return ptrcode;
}

instr *compile_call0 (instr *ptrcode, int (*f)())
{
 return compile_call (ptrcode, f, 0, 0);
}


#endif

#ifdef COMPX86

void setbradr (instr *from, instr *to)
{
 int ofs;
/*
 ofs = to - (from + 4);
 from[2] = ofs & 0xFF;;
 from[3] = (ofs & 0xFF00) >> 8;
*/
 ofs = to - (from + 5);
 printf ("from=%X to=%X ofs=%X\n", from, to, ofs);
 from[4] = ofs;
}

codeptr compile_call0 (codeptr cp, int (*f)())
{
 any a;
 int d;
 a.intf = f;
 d=a.cp-(cp+3);
 *cp++ = 0xE8;
 *cp++ = d & 0xFF;
 *cp++ = (d & 0xFF00) >> 8;
 return cp;
}

codeptr compile_call (codeptr ptrcode, int (*f)(), int regs, int res)
{
 return compile_call0 (ptrcode, f);
}

#endif


#ifdef PPC 
ft getprocadr (wchar_t *mn, wchar_t *fn)
{
HINSTANCE module;
int (*f)();
 module = GetModuleHandle (mn);
 if (module != NULL)
  f = GetProcAddress (module, fn);
 else
 {
  module = LoadLibrary (mn);
  if (module != NULL)
   f = GetProcAddress (module, fn);
  else
  {
   /* printf ("getprocadr: undefined function\n"); */
   f = NULL;
  }
 }
 return f; 
}
#else
#ifdef DEVCPP
ft getprocadr (char *mn, char *fn)
{
HINSTANCE module;
int (*f)();
 module = GetModuleHandle (mn);
 if (module != NULL)
  f = GetProcAddress (module, fn);
 else
 {
  module = LoadLibrary (mn);
  if (module != NULL)
   f = GetProcAddress (module, fn);
  else
  {
   /* printf ("getprocadr: undefined function\n"); */
   f = NULL;
  }
 }
 return f; 
}
#else
#ifdef LINUX
ft getprocadr (char *ln, char *fn)
{
void *hl;
int (*fp)();
char *error; 
 /* printf ("getprocadr library=(%s) function=(%s)\n", ln, fn); */
 hl = dlopen (ln, RTLD_LAZY);
 if (!hl)
  return NULL;
 else
 {
  fp = dlsym (hl, fn);
  error = dlerror();
  if (error != NULL)
  {
   printf ("Error getprocadr: %s.\n");
   return NULL;
  }
  else
  {
   /* dlclose (hl); */
   return fp;
  }
 }
}
#else
ft getprocadr (char *mn, char *fn)
{
 return NULL;
}
#endif
#endif
#endif

codeptr c_getprocadr (codeptr cp)
{
#ifdef INTERP
 *cp++ = code_getprocadr;
#else
 cp = compile_call0 (cp, (int(*)())getprocadr);
#endif
 return cp;
}


#ifdef INTERP

codeptr c_getchar (codeptr cp)
{
 trace ("c_getchar");
 if (f_tasm != NULL)
  fprintf (f_tasm, " mov ah,1\n int 21h\n mov ah,0\n");
 if (f_asmi != NULL)
  fprintf (f_asmi, " call getchar\n mov %%ah, 0\n");
 if (f_asml != NULL)
  fprintf (f_asml, " call getchar\n mov $0,%%ah\n");
 if (f_x86 != NULL)
  fprintf (f_x86, " call getchar\n .byte 0xB4, 0\n");
 *cp++ = code_getchar;
 return cp;
}

codeptr c_putchar (codeptr cp)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " mov dx,ax\n mov ah,2\n int 21h\n");
 if (f_asmi != NULL)
  fprintf (f_asmi, " mov DWORD PTR [%%esp], %%eax\n call putchar\n");
 if (f_asml != NULL)
  fprintf (f_asml, " movl %%eax,(%%esp)\n call putchar\n");
 if (f_x86 != NULL)
  fprintf (f_x86, " movl %%eax,(%%esp)\n call putchar\n");
 *cp++ = code_putchar;
 return cp;
}

#else
codeptr c_getchar (codeptr cp)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " mov ah,1\n int 21h\n mov ah,0\n");
 if (f_asml != NULL)
  fprintf (f_asml, " call getchar\n mov $0,%%ah\n");
 cp = compile_call (cp, (int(*)())f_getchar, 0, 0);
 return cp;
}

codeptr c_putchar (codeptr cp)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " mov dx,ax\n mov ah,2\n int 21h\n");
 if (f_asml != NULL)
  fprintf (f_asml, " movl %%eax,(%%esp)\n call putchar\n");
#ifdef COMPX86
 cp = c_push_r0 (cp);
#endif
 cp = compile_call (cp, (int(*)())f_putchar, 0, 0);
#ifdef COMPX86
 cp = c_pop_r2 (cp);
#endif
 return cp;
}

codeptr c_print (codeptr cp)
{
 cp = compile_call (cp, (int(*)())f_print,0,0);
 return cp;
}

#endif

codeptr c_getword (codeptr cp)
{
 if (f_tasm != NULL)
 {
  /* fprintf (f_tasm, " call getword\n mov si,[gpw]\n"); */
  /* fprintf (f_tasm, " call _getword\n"); */
  asm_call_ext ("getword");
  fprintf (f_tasm, " mov si,ax\n");
 }

#ifdef INTERP
 *cp++ = code_getword;
#else
 cp = compile_call (cp, (int(*)())getword, 0, 0);
 cp = c_mov_ra_im (cp, (int)&gwri, "");
 cp = c_mov_r0_cont_ra (cp);
 cp = c_mov_ra_im (cp, (int)&gpw, "");
 cp = c_mov_ra_cont_ra (cp);
 cp=compile_call(cp,(int(*)())f_dummyprint,0,0);
#endif
 return cp;
}

codeptr c_getwordstr (codeptr cp)
{
 if (f_tasm != NULL)
 {
  /* fprintf (f_tasm, " call getword\n mov si,[gpw]\n"); */
  /* fprintf (f_tasm, " call _getword\n"); */
  asm_call_ext ("getwordstr");
  fprintf (f_tasm, " mov si,ax\n");
 }

#ifdef INTERP
 *cp++ = code_getwordstr;
#else
 cp = compile_call (cp, (int(*)())getwordstr, 0, 0);
 cp = c_mov_ra_im (cp, (int)&gwri, "");

 cp = c_mov_r0_cont_ra (cp);
 cp = c_mov_ra_im (cp, (int)&gpw, "");
 cp = c_mov_ra_cont_ra (cp);
 cp=compile_call(cp,(int(*)())f_dummyprint,0,0);
#endif
 return cp;
}

codeptr c_scanhex (codeptr cp)
{
 if (f_tasm != NULL)
  /* fprintf (f_tasm, " call _scanhex\n"); */
  asm_call_ext ("scanhex");
#ifdef INTERP
 *cp++ = code_scanhex;
#else
 cp = compile_call0 (cp, (int(*)())f_scanhex);
#endif
 return cp;
}

FILE * f_fopen (int mode, char *fn)
{
 FILE *fd;
 switch (mode & 3)
 {
  case 0:
   fd = fopen (fn, "r");
   break;
  case 1:
   fd = fopen (fn, "wb");
   break;
  case 2:
   fd = fopen (fn, "r+b");
   break;
  }
 return fd;
}

codeptr c_fopen (codeptr cp)
{
 if (f_tasm != NULL)
  asm_call_ext ("f_fopen");
#ifdef INTERP
 *cp++ = code_fopen;
#else
 cp = compile_call0 (cp, (int(*)())f_fopen);
#endif
 return cp;
}

int f_fclose (FILE *fd)
{
 return fclose(fd);
}

codeptr c_fclose (codeptr cp)
{
 if (f_tasm != NULL)
  asm_call_ext ("f_fclose");
#ifdef INTERP
 *cp++ = code_fclose;
#else
#ifdef C_COMPX86
 
#endif
 cp = compile_call0 (cp, (int(*)())f_fclose);
#endif
 return cp;
}

int f_fgetc (FILE *fd)
{
 return fgetc(fd);
}

codeptr c_fgetc (codeptr cp)
{
 if (f_tasm != NULL)
  asm_call_ext("f_fgetc");
#ifdef INTERP
 *cp++ = code_fgetc;
#else
 cp = compile_call0 (cp, (int(*)())f_fgetc);
#endif
 return cp;
}

int f_fputc (FILE *fd, char c)
{
 return fputc (c, fd);
}

codeptr c_fputc (codeptr cp)
{
 if (f_tasm != NULL)
  asm_call_ext("f_fputc");
#ifdef INTERP
 *cp++ = code_fputc;
#else
 cp = compile_call0 (cp, (int(*)())f_fputc);
#endif
 return cp;
}

#ifdef SOCKET

int f_socket (int domain, int type, int protocol)
{
 return socket (domain, type, protocol);
}

codeptr c_socket (codeptr cp)
{
#ifdef INTERP
 *cp++ = code_socket;
#else
 cp = compile_call0 (cp, (int(*)())f_socket);
#endif
}

int f_closesocket (int sock)
{
 return close (sock);
}

codeptr c_closesocket (codeptr cp)
{
#ifdef INTERP
 *cp++ = code_closesocket;
#else
 cp = compile_call0 (cp, (int(*)())f_closesocket);
#endif
}

int f_listen (int sock, int backlog)
{
 return listen (sock, backlog);
}

codeptr c_listen (codeptr cp)
{
#ifdef INTERP
 *cp++ = code_listen;
#else
 cp = compile_call0 (cp, (int(*)())f_listen);
#endif
}

int f_accept (int sock, struct sockaddr *sa, int *plen)
{
 return accept (sock, sa, plen);
}

codeptr c_accept (codeptr cp)
{
#ifdef INTERP
 *cp++ = code_accept;
#else
 cp = compile_call0 (cp, (int(*)())f_accept);
#endif
}

int f_bind (int sock, struct sockaddr *sa, int len)
{
 return bind (sock, sa, len);
}

codeptr c_bind (codeptr cp)
{
#ifdef INTERP
 *cp++ = code_bind;
#else
 cp = compile_call0 (cp, (int(*)())f_bind);
#endif
}

int f_connect (int sock, struct sockaddr *sa, int len)
{
 return connect (sock, sa, len);
}

codeptr c_connect (codeptr cp)
{
#ifdef INTERP
 *cp++ = code_accept;
#else
 cp = compile_call0 (cp, (int(*)())f_connect);
#endif
}

int f_recv (int sock, char *data, int len, int flags)
{
 return recv (sock, data, len, flags);
}

codeptr c_recv (codeptr cp)
{
#ifdef INTERP
 *cp++ = code_recv;
#else
 cp = compile_call0 (cp, (int(*)())f_recv);
#endif
}

int f_send (int sock, char *data, int len, int flags)
{
 return send (sock, data, len, flags);
}

codeptr c_send (codeptr cp)
{
#ifdef INTERP
 *cp++ = code_send;
#else
 cp = compile_call0 (cp, (int(*)())f_send);
#endif
}

#endif

#ifdef JNI

int CallMethodA (JNIEnv *env, jobject obj, jmethodID mid, jvalue *args, int type)
{
 switch (type)
 {
  case 0:
   (*env)->CallVoidMethod (env, obj, mid);
   return 0;
  case 1:
   return (int) (*env)->CallObjectMethodA (env, obj, mid, args);
  case 2:
   return (int) (*env)->CallBooleanMethodA (env, obj, mid, args);
  case 3:
   return (int) (*env)->CallByteMethodA (env, obj, mid, args);
  case 4:
   return (int) (*env)->CallCharMethodA (env, obj, mid, args);
  case 5:
   return (int) (*env)->CallShortMethodA (env, obj, mid, args);
  case 6 : 
   return (*env)->CallIntMethodA (env, obj, mid, args);
  case 7:
   return (int) (*env)->CallLongMethodA (env, obj, mid, args);
  case 8:
   return (int) (*env)->CallFloatMethodA (env, obj, mid, args);
  case 9:
   return (int) (*env)->CallDoubleMethodA (env, obj, mid, args);
  default:
   return 0;
 }
}

codeptr c_findclass (codeptr cp)
{
 *cp++ = code_findclass;
}

codeptr c_getmethodid (codeptr cp)
{
 *cp++ = code_getmethodid;
}

codeptr c_callmethoda (codeptr cp)
{
 *cp++ == code_callmethoda;
}

codeptr c_getstringutfchars (codeptr cp)
{
 *cp++ = code_getstringutfchars;
}

codeptr c_newstringutf (codeptr cp)
{
 trace ("c_newstringutf");
 *cp++ = code_newstringutf;
}



#endif

codeptr c_resetdraw (codeptr cp)
{
 /* trace ("c_resetdraw"); */
#ifdef INTERP
 *cp++ = code_resetdraw;
#endif
 return cp;
}

codeptr c_draw (codeptr cp)
{
 /* trace ("c_draw"); */ 
#ifdef INTERP
 *cp++ = code_draw;
#endif
 return cp;
}

codeptr c_invalidate (codeptr cp)
{
 /* trace ("c_invalidate"); */ 
#ifdef INTERP
 *cp++ = code_invalidate;
#endif
 return cp;
}



void f_dummy(void)
{
}

codeptr c_call_dummy(codeptr cp)
{
/*
 if (f_tasm != NULL)
  asm_call_dummy();
*/
 /*cp = compile_call_dummy (cp);*/
 cp = compile_call (cp, (int(*)())f_dummy, 0, 0);
 return cp;
}

codeptr c_printhex (codeptr cp)
{
 if (f_tasm != NULL)
 {
  fprintf(f_tasm," push ax\n");
  asm_call_ext ("printhex");
  /* fprintf(f_tasm," pop cx\n"); */
  fprintf (f_tasm, " inc sp\n inc sp\n");
 }
#ifdef INTERP
 *cp++ = code_printhex;
#else
#ifdef COMPX86
 cp = c_push_r0 (cp);
#endif
 cp = compile_call (cp, (int(*)())f_printhex, 0, 0);
#ifdef COMPX86
 /* cp = c_pop_r2 (cp); */
 *cp++ = 0x44;
 *cp++ = 0x44;
#endif
#endif
 return cp;
}

void f_printdec (int x)
{
 /* printf (" %d ", x); */
 trace ("begin f_printdec");
 sprintf (buf, " %d ", x);
 trace (buf);
 output (buf);
 /* printf("printdec(%d)",x); */
 trace ("end f_printdec");
}

codeptr c_printdec (codeptr cp)
{
 if (f_tasm != NULL)
 {
  fprintf (f_tasm, " push ax\n");
  asm_call_ext ("printdec");
  /* fprintf (f_tasm, " pop cx\n"); */
  fprintf (f_tasm, " inc sp\n inc sp\n");
 }
#ifdef INTERP
 *cp++ = code_printdec;
#else
 cp = compile_call (cp, (int(*)())f_printdec, 0, 0);
#endif
 return cp;
}

int f_sscandec (char *s)
{
 int x;
 sscanf (s, "%d", &x);
 return x;
}

codeptr c_sscandec (codeptr cp)
{
 if (f_tasm != NULL)
 {
  fprintf (f_tasm, " push ax\n");
  asm_call_ext ("sscandec");
  fprintf (f_tasm, " pop cx\n");
 }
#ifdef INTERP
 *cp++ = code_sscandec;
#else
 cp = compile_call (cp, (int(*)())f_sscandec, 0, 0);
#endif
 return cp;
}

void f_dummyprint(void)
{
 /* printf("#",);*/
 FILE *f;
 f=fopen("dummy.txt","w");
 fclose(f);
 clearcache();
}

codeptr c_dummyprint(codeptr cp)
{
#ifndef JNI
 cp=compile_call(cp,(int(*)())f_dummyprint,0,0);
#endif
 return cp;
}

codeptr c_mov_r0_im (codeptr cp, long im, char *l)
{
 if (f_tasm != NULL)
 {
  if (l == 0 || *l == 0)
   fprintf (f_tasm, " mov ax,0%Xh\n", im);
  else
   fprintf (f_tasm, " lea ax,[%s]\n", l);
 }
 if (f_asmi != NULL)
 {
  if (*l == 0)
   fprintf (f_asmi, " mov %%ax,0x%X\n", im);
  else
   fprintf (f_asmi, " lea %%ax,[%s]\n", l);
 }
 if (f_asml != NULL)
 {
  if (*l == 0)
   fprintf (f_asml, " mov $0x%X,%%ax\n", im);
  else
   fprintf (f_asml, " lea (%s),%%ax\n", l);
 }
 if (f_x86 != NULL)
 {
  if (*l == 0)
   fprintf (f_x86, " .byte 0xB8, 0x%X, 0x%X\n", im & 0xFF, (im & 0xFF00) >> 8);
  else
  {
   int d;
   /* d = lab[l] - cod; */
   /* fprintf (f_x86, " .byte 0xB8, 0x%X, 0x%X\n", d & 0xFF, (d & 0xFF00) >> 8); */
   fprintf (f_x86, " .byte 0xB8\n .word %s-main\n", l);
   /* fprintf (f_x86, " .byte 0xB8, %c, 0\n", l); */
  }
 }
#ifdef INTERP
 *cp++ = code_mov_r0_im;
 *cp = im;
 /*
 printf ("im=%lX ",im); 
 printf ("*cp=%lX\n", *cp); 
 */
 cp++;
#endif
#ifdef COMPARM
 *cp++ = 0xE59F0000;
 *cp++ = 0xEA000000;
 *cp++ = im;
#endif
#ifdef COMPX86
 *cp++ = 0xB8;
 *cp++ = im & 0xFF;
 *cp++ = (im & 0xFF00) >> 8;
#endif
 return cp;
}

codeptr c_mov_r1_im (codeptr cp, long im, char *l)
{
 if (f_tasm != NULL)
 {
  if (*l == 0)
   fprintf (f_tasm, " mov dx,%Xh\n", im);
  else
   fprintf (f_tasm, " lea dx,[%s]\n", l);
 }
 if (f_asmi != NULL)
 {
  if (*l == 0)
   fprintf (f_asmi, " mov %%dx,0x%X\n", im);
  else
   fprintf (f_asmi, " lea %%dx,[%s]\n", l);
 }
 if (f_asml != NULL)
 {
  if (*l == 0)
   fprintf (f_asml, " mov $0x%X,%%dx\n", im);
  else
   fprintf (f_asml, " lea (%s),%%dx\n", l);
 }
 if (f_x86 != NULL)
 {
  if (*l == 0)
   fprintf (f_x86, " .byte 0xBA, 0x%X, 0x%X\n", im & 0xFF, (im & 0xFF00) >> 8);
  else
  {
   int d;
   /* d = lab[l] - cod; */
   /* fprintf (f_x86, " .byte 0xBB, 0x%X, 0x%X\n", d & 0xFF, (d & 0xFF00) >> 8); */
   fprintf (f_x86, " .byte 0xBA\n .word %s-main\n", l);
   /* fprintf (f_x86, " .byte 0xBB, %c, 0\n", l); */
  }
 }
#ifdef INTERP
 *cp++ = code_mov_r1_im;
 *cp++ = im;
#endif
#ifdef COMPARM
 *cp++ = 0xE59F1000;
 *cp++ = 0xEA000000;
 *cp++ = im;
#endif
#ifdef COMPX86
 *cp++ = 0xBA;
 *cp++ = im & 0xFF;
 *cp++ = (im & 0xFF00) >> 8;
#endif
 return cp;
}

codeptr c_mov_ra_im (codeptr cp, long im, char *l)
{
 /* printf("c_mov_ra_im\n"); */
 if (f_tasm != NULL)
 {
  if (*l == 0)
   fprintf (f_tasm, " mov si,%Xh\n", im);
  else
   fprintf (f_tasm, " lea si,[%s]\n", l);
 }
 if (f_asmi != NULL)
 {
  if (*l == 0)
   fprintf (f_asmi, " mov %%si,0x%X\n", im);
  else
   fprintf (f_asmi, " lea %%si,[%s]\n", l);
 }
 if (f_asml != NULL)
 {
  if (*l == 0)
   fprintf (f_asml, " mov $0x%X,%%si\n", im);
  else
   fprintf (f_asml, " lea (%s),%%dx\n", l);
 }
 if (f_x86 != NULL)
 {
  if (*l == 0)
   fprintf (f_x86, " .byte 0xBE, 0x%X, 0x%X\n", im & 0xFF, (im & 0xFF00) >> 8);
  else
  {
   int d;
   /* d = lab[l] - cod; */
   /* fprintf (f_x86, " .byte 0xBB, 0x%X, 0x%X\n", d & 0xFF, (d & 0xFF00) >> 8); */
   fprintf (f_x86, " .byte 0xBE\n .word %s-main\n", l);
   /* fprintf (f_x86, " .byte 0xBB, %c, 0\n", l); */
  }
 }
 /* printf("end write files\n"); */
#ifdef INTERP
 /* printf("interp 1 cp=%X\n",cp); */
 *cp++ = code_mov_ra_im;
 /* printf("interp 2\n"); */
 *cp++ = im;
 /* printf("interp 3\n"); */
#endif
#ifdef COMPARM
 /* printf("comparm 1 cp=%X\n",cp); */
 *cp++ = 0xE59FA000;
 /* printf("comparm 2\n"); */
 *cp++ = 0xEA000000;
 /* printf("comparm 3\n"); */
 *cp++ = im;
 /* printf("comparm 4\n"); */
#endif
#ifdef COMPX86
 *cp++ = 0xBE;
 *cp++ = im & 0xFF;
 *cp++ = (im & 0xFF00) >> 8;
#endif
 /* printf("end c_mov_ra_im\n");*/
 return cp;
}

codeptr c_mov_ra_sva (codeptr cp)
{
 if (f_tasm != NULL)
 {
  /* fprintf (f_tasm, " lea si,[_sva]\n"); */
  fprintf (f_tasm, " mov [word ptr sax],ax\n");
  asm_call_ext ("getsva");
  fprintf (f_tasm, " mov si,ax\n");
  fprintf (f_tasm, " mov ax,[word ptr sax]\n");
 }
#ifdef INTERP
 *cp++ = code_mov_ra_sva;
#endif
#ifdef COMPARM
 *cp++ = 0xE59FA000;
 *cp++ = 0xEA000000;
 *cp++ = (instr)sva;
#endif
 return cp;
}

codeptr c_q_mov_r0_imr0 (codeptr cp)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " push cx\n mov cl,0B8h\n mov [di],cl\n inc di\n mov [di],al\n inc di\n mov[di],ah\n inc di\n pop cx\n");
#ifdef INTERP
 *cp++ = code_q_mov_r0_imr0;
#endif
#ifdef COMPARM
 *cp++ = 0xE59F9000; /* R9=[RF] */
 *cp++ = 0xEA000000; /* GOTO RF */
 *cp++ = 0xE59F0000; /* R0=[RF] */
 *cp++ = 0xE58C9000; /* [RC]=R9 */
 *cp++ = 0xE28CC004; /* RC=RC+4 */
 *cp++ = 0xE59F9000; /* R9=[RF] */
 *cp++ = 0xEA000000; /* GOTO RF */
 *cp++ = 0xEA000000; /* GOTO RF */
 *cp++ = 0xE58C9000; /* [RC]=R9 */
 *cp++ = 0xE28CC004; /* RC=RC+4 */
 *cp++ = 0xE58C0000; /* [RC]=R0 */
 *cp++ = 0xE28CC004; /* RC=RC+4 */
#endif
#ifdef COMPX86
 *cp++ = 0xB1; *cp++ = 0xB8; /* MOV CL,B8 */
 *cp++ = 0x88; *cp++ = 0x0D; /* MOV [DI],CL */
 *cp++ = 0x47; /* INC DI */
 *cp++ = 0x88; *cp++ = 0x05; /* MOV [DI],AL */
 *cp++ = 0x47; /* INC DI */
 *cp++ = 0x88; *cp++ = 0x25; /* MOV [DI],AH */
 *cp++ = 0x47; /* INC DI */
#endif
 return cp;
}

codeptr c_q_mov_r1_imr0 (codeptr cp)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " push cx\n mov cl,0BAh\n mov [di],cl\n inc di\n mov [di],al\n inc di\n mov[di],ah\n inc di\n pop cx\n");
#ifdef INTERP
 *cp++ = code_q_mov_r1_imr0;
#endif
#ifdef COMPARM
 *cp++ = 0xE59F9000; /* R9=[RF] */
 *cp++ = 0xEA000000; /* GOTO RF */
 *cp++ = 0xE59F1000; /* R1=[RF] */
 *cp++ = 0xE58C9000; /* [RC]=R9 */
 *cp++ = 0xE28CC004; /* RC=RC+4 */
 *cp++ = 0xE59F9000; /* R9=[RF] */
 *cp++ = 0xEA000000; /* GOTO RF */
 *cp++ = 0xEA000000; /* GOTO RF */
 *cp++ = 0xE58C9000; /* [RC]=R9 */
 *cp++ = 0xE28CC004; /* RC=RC+4 */
 *cp++ = 0xE58C0000; /* [RC]=R0 */
 *cp++ = 0xE28CC004; /* RC=RC+4 */
#endif
#ifdef COMPX86
 *cp++ = 0xB1; *cp++ = 0xBA; /* MOV CL,BA */
 *cp++ = 0x88; *cp++ = 0x0D; /* MOV [DI],CL */
 *cp++ = 0x47; /* INC DI */
 *cp++ = 0x88; *cp++ = 0x05; /* MOV [DI],AL */
 *cp++ = 0x47; /* INC DI */
 *cp++ = 0x88; *cp++ = 0x25; /* MOV [DI],AH */
 *cp++ = 0x47; /* INC DI */
#endif
 return cp;
}

codeptr c_q_mov_ra_imr0 (codeptr cp)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " push cx\n mov cl,0BEh\n mov [di],cl\n inc di\n mov [di],al\n inc di\n mov[di],ah\n inc di\n pop cx\n");
#ifdef INTERP
 *cp++ = code_q_mov_ra_imr0;
#endif
#ifdef COMPARM
 *cp++ = 0xE59F9000; /* R9=[RF] */
 *cp++ = 0xEA000000; /* GOTO RF */
 *cp++ = 0xE59FA000; /* RA=[RF] */
 *cp++ = 0xE58C9000; /* [RC]=R9 */
 *cp++ = 0xE28CC004; /* RC=RC+4 */
 *cp++ = 0xE59F9000; /* R9=[RF] */
 *cp++ = 0xEA000000; /* GOTO RF */
 *cp++ = 0xEA000000; /* GOTO RF */
 *cp++ = 0xE58C9000; /* [RC]=R9 */
 *cp++ = 0xE28CC004; /* RC=RC+4 */
 *cp++ = 0xE58C0000; /* [RC]=R0 */
 *cp++ = 0xE28CC004; /* RC=RC+4 */
#endif
#ifdef COMPX86
 *cp++ = 0xB1; *cp++ = 0xBE; /* MOV CL,BE */
 *cp++ = 0x88; *cp++ = 0x0D; /* MOV [DI],CL */
 *cp++ = 0x47; /* INC DI */
 *cp++ = 0x88; *cp++ = 0x05; /* MOV [DI],AL */
 *cp++ = 0x47; /* INC DI */
 *cp++ = 0x88; *cp++ = 0x25; /* MOV [DI],AH */
 *cp++ = 0x47; /* INC DI */
#endif
 return cp;
}


int reg_num_x86[] = { 0, 2, 1, -1, -1, -1, -1, -1, -1, -1, 6, 3, 7, 0, 0, 0 };

const char * reg_name_x86 [] = { "ax", "dx", "cx", "", "", "", "", "", "", "bp", "si", "bx", "di", "sp" };

codeptr c_mov_r_r (codeptr cp, int rd, int rs)
{
 if (f_tasm != NULL)
  fprintf (f_tasm," mov %s,%s\n", reg_name_x86[rd], reg_name_x86[rs]);
 if (f_asmi != NULL)
  fprintf (f_asmi, " mov %%%s,%%%s\n", reg_name_x86[rd], reg_name_x86[rs]);
 if (f_asml != NULL)
  fprintf (f_asml, " mov %%%s,%%%s\n", reg_name_x86[rs], reg_name_x86[rd]);
 if (f_x86 != NULL)
  /* fprintf (f_x86, " .byte 0x89, 0xCA\n"); */
  fprintf (f_x86, " .byte 0x8B, 0x%X\n", 0xC0 | (rd<<3) | rs);
#ifdef INTERP
 *cp++ = code_mov_r_r | (rd<<8) | rs;
#endif
#ifdef COMPARM
  /* *cp++ = 0xE1A01002; */
  *cp++ = 0xE1A00000 | (rd<<12) | rs;
#endif
#ifdef COMPX86
 /*
 *cp++ = 0x89;
 *cp++ = 0xCA;
 */
 *cp++ = 0x8B;
 *cp++ = 0xC0 | (rd<<3) | rs;
#endif
 return cp;
}
codeptr c_mov_r1_r0 (codeptr cp)
{
 if (f_tasm != NULL)
  fprintf (f_tasm," mov dx,ax\n");
 if (f_asmi != NULL)
  fprintf (f_asmi, " mov %%dx,%%ax\n");
 if (f_asml != NULL)
  fprintf (f_asml, " mov %%ax,%%dx\n");
 if (f_x86 != NULL)
  fprintf (f_x86, " .byte 0x89, 0xC2\n");
#ifdef INTERP
 *cp++ = code_mov_r1_r0;
#endif
#ifdef COMPARM
  *cp++ = 0xE1A01000;
#endif
#ifdef COMPX86
 *cp++ = 0x89;
 *cp++ = 0xC2;
#endif
 return cp;
}

/* [rc+=n] = code(r1=r0) */
codeptr c_q_mov_r1_r0 (codeptr cp)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " mov cl,89h\n mov [di],cl\n inc di\n mov cl,C3h\n mov [di],cl\n inc di\n");
 if (f_asmi != NULL)
  fprintf (f_asmi, " mov %%cl,0x89\n mov [%%di],%%cl\n inc %%di\n mov %%cl,0xC3\n mov [%%di],%%cl\n inc %%di\n");
 if (f_asml != NULL)
  fprintf (f_asml, " mov $0x89,%%cl\n mov %%cl,(%%di)\n inc %%di\n mov $0xC3,%%cl\n mov %%cl,(%%di)\n inc %%di\n");
 if (f_x86 != NULL)
  fprintf (f_x86, " .byte 0xB1, 0x89, 0x88, 0x0D, 0x47, 0xB1, 0xC2, 0x88, 0x0D, 0x47\n");
#ifdef INTERP
 *cp++ = code_q_mov_r1_r0;
#endif
#ifdef COMPARM
 *cp++ = 0xE59F9000; /* R9 = [RF] */
 *cp++ = 0xEA000000; /* GOTO RF */
 *cp++ = 0xE1A01000; /* code of R1=R0 to load in R9 */
 *cp++ = 0xE58C9000; /* [RC]=R9 */
 *cp++ = 0xE28CC004; /* RC=RC+4 */
#endif
#ifdef COMPX86
 *cp++ = 0xB1;
 *cp++ = 0x89;
 *cp++ = 0x88;
 *cp++ = 0x0D;
 *cp++ = 0x47;
 *cp++ = 0xB1;
 *cp++ = 0xC2;
 *cp++ = 0x88;
 *cp++ = 0x0D;
 *cp++ = 0x47;
#endif
 return cp;
}

codeptr c_mov_r0_cont_ra (codeptr cp)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " mov ax,[si]\n");
 if (f_asmi != NULL)
  fprintf (f_asmi, " mov %%ax,[%%si]\n");
 if (f_asml != NULL)
  fprintf (f_asml, " mov (%%si),%%ax\n");
 if (f_x86 != NULL)
  fprintf (f_x86, " .byte 0x8B, 0x04\n");
#ifdef INTERP
 *cp++ = code_mov_r0_cont_ra;
#endif
#ifdef COMPARM
 *cp++ = 0xE59A0000;
#endif
#ifdef COMPX86
 *cp++ = 0x8B;
 *cp++ = 0x04;
#endif
 return cp;
}

codeptr c_mov_r0_byte_cont_ra (codeptr cp)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " mov al,[byte ptr si]\nmov ah,0\n");
 if (f_x86 != NULL)
  fprintf (f_x86, " .byte 0x8A, 0x04, 0xB4, 0x00\n");
#ifdef INTERP
 *cp++ = code_mov_r0_byte_cont_ra;
#endif
#ifdef COMPARM
 *cp++ = 0xE55A0000;
#endif
#ifdef COMPX86
 *cp++ = 0x8A;
 *cp++ = 0x04;
 *cp++ = 0xB4;
 *cp++ = 0x00;
#endif
 return cp;
}

codeptr c_mov_ra_cont_ra (codeptr cp)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " mov si,[si]\n");
 if (f_asmi != NULL)
  fprintf (f_asmi, " mov %%si,[%%si]\n");
 if (f_asml != NULL)
  fprintf (f_asml, " mov (%%si),%%si\n");
 if (f_x86 != NULL)
  fprintf (f_x86, " .byte 0x8B, 0x34\n");
#ifdef INTERP
 *cp++ = code_mov_ra_cont_ra;
#endif
#ifdef COMPARM
 *cp++ = 0xE59AA000;
#endif
#ifdef COMPX86
 *cp++ = 0x8B;
 *cp++ = 0x34;
#endif
 return cp;
}

codeptr c_mov_cont_ra_r0 (codeptr cp)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " mov [si],ax\n");
 if (f_asmi != NULL)
  fprintf (f_asmi, " mov [%%si],%%ax\n");
 if (f_asml != NULL)
  fprintf (f_asml, " mov %%ax,(%%si)\n");
 if (f_x86 != NULL)
  fprintf (f_x86, " .byte 0x89, 0x04\n");
#ifdef INTERP
 *cp++ = code_mov_cont_ra_r0;
#endif
#ifdef COMPARM
 *cp++ = 0xE58A0000;
#endif
#ifdef COMPX86
 *cp++ = 0x89;
 *cp++ = 0x04;
#endif
 return cp;
}

codeptr c_mov_byte_cont_ra_r0 (codeptr cp)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " mov [byte ptr si],al\n");
 if (f_x86 != NULL)
  fprintf (f_x86, " .byte 0x88, 0x04\n");
#ifdef INTERP
 *cp++ = code_mov_byte_cont_ra_r0;
#endif
#ifdef COMPARM
 *cp++ = 0xE54A0000;
#endif
#ifdef COMPX86
 *cp++ = 0x88;
 *cp++ = 0x04;
#endif
 return cp;
}

codeptr c_mov_r0_cont_ra_plus_im (codeptr cp, int im)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " mov ax,[si+0%Xh]\n", im);
 if (f_asmi != NULL)
  fprintf (f_asmi, " mov %%ax,[%%si+0x%X]\n", im);
 if (f_asml != NULL)
  fprintf (f_asml, " mov (%%si+0x%X),%%ax\n", im);
 if (f_x86 != NULL)
  fprintf (f_x86, " .byte 0x8B, 0x44, 0x%X\n", im);
#ifdef INTERP
 *cp++ = code_mov_r0_cont_ra_plus_im;
 *cp++ = (instr)im;
#endif
#ifdef COMPARM
 *cp++ = 0xE59A0000 | im;
#endif
#ifdef COMPX86
 *cp++ = 0x8B;
 *cp++ = 0x44;
 *cp++ = im;
#endif
 return cp;
}

codeptr c_mov_cont_ra_plus_im_r0 (codeptr cp, int im)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " mov [si+%Xh],ax\n", im);
 if (f_asmi != NULL)
  fprintf (f_asmi, " mov [%%si+0x%X],%%ax\n", im);
 if (f_asml != NULL)
  fprintf (f_asml, " mov %%ax,(%%si+0x%X)\n", im);
 if (f_x86 != NULL)
  fprintf (f_x86, " .byte 0x89, 0x44; 0x%X\n", im);
#ifdef INTERP
 *cp++ = code_mov_cont_ra_plus_im_r0;
 *cp++ = (instr)im;
#endif
#ifdef COMPARM
 *cp++ = 0xE58A0000 | im;
#endif
#ifdef COMPX86
 *cp++ = 0x89;
 *cp++ = 0x44;
 *cp++ = im;
#endif
 return cp;
}

codeptr c_mov_r0_cont_rb_inc (codeptr cp)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " mov ax,[bx]\n add bx,2\n");
#ifdef INTERP
 *cp++ = code_mov_r0_cont_rb_inc;
#endif
#ifdef COMPARM
 *cp++ = 0xE8BB0001;
#endif
#ifdef COMPX86
 *cp++ = 0x8B; /* mov ax,[bx] */
 *cp++ = 0x07;
 *cp++ = 0x83; /* add bx,2 */
 *cp++ = 0xC3;
 *cp++ = 0x02;
#endif
 return cp;
}

codeptr c_mov_cont_dec_rb_r0 (codeptr cp)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " sub bx,2\n mov [bx],ax\n");
#ifdef INTERP
 *cp++ = code_mov_cont_dec_rb_r0;
#endif
#ifdef COMPARM
 *cp++ = 0xE92B0001;
#endif
#ifdef COMPX86
 *cp++ = 0x83; /* sub bx,2 */
 *cp++ = 0xEB;
 *cp++ = 0x02;
 *cp++ = 0x89; /* mov [bx],ax */
 *cp++ = 0x07;
#endif
 return cp;
}

codeptr c_mov_r1_cont_rb_inc (codeptr cp)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " mov dx,[bx]\n add bx,2\n");
#ifdef INTERP
 *cp++ = code_mov_r1_cont_rb_inc;
#endif
#ifdef COMPARM
 *cp++ = 0xE8BB0002;
#endif
#ifdef COMPX86
 *cp++ = 0x8B; /* mov dx,[bx] */
 *cp++ = 0x17;
 *cp++ = 0x83; /* add bx,2 */
 *cp++ = 0xC3;
 *cp++ = 0x02;
#endif
 return cp;
}

codeptr c_mov_ra_cont_rb_inc (codeptr cp)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " mov si,[bx]\n add bx,2\n");
#ifdef INTERP
 *cp++ = code_mov_ra_cont_rb_inc;
#endif
#ifdef COMPARM
 *cp++ = 0xE8BB0400;
#endif
#ifdef COMPX86
 *cp++ = 0x8B; /* mov si,[bx] */
 *cp++ = 0x37;
 *cp++ = 0x83; /* add bx,2 */
 *cp++ = 0xC3;
 *cp++ = 0x02;
#endif
 return cp;
}

codeptr c_mov_cont_dec_rb_r1 (codeptr cp)
{
 if (f_tasm != NULL)
 fprintf (f_tasm, " sub bx,2\n mov [bx],dx\n");
#ifdef INTERP
 *cp++ = code_mov_cont_dec_rb_r1;
#endif
#ifdef COMPARM
 *cp++ = 0xE92B0002;
#endif
#ifdef COMPX86
 *cp++ = 0x83; /* sub bx,2 */
 *cp++ = 0xEB;
 *cp++ = 0x02;
 *cp++ = 0x89; /* mov [bx],dx */
 *cp++ = 0x17;
#endif
 return cp;
}

codeptr c_mov_cont_rc_inc_r0 (codeptr cp)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " mov [di],ax\n inc di\n");
#ifdef INTERP
 *cp++ = code_mov_cont_rc_inc_r0;
#endif
#ifdef COMPARM
 *cp++ = 0xE8AC0001;
#endif
#ifdef COMPX86
 *cp++ = 0x89; *cp++ = 0x05; /* mov [di],ax */
 *cp++ = 0x47; /* inc di */
#endif
 return cp;
}

codeptr c_add_r0_r1 (codeptr cp)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " add ax,dx\n");
 if (f_asmi != NULL)
  fprintf (f_asmi, " add %%ax,%%dx\n");
 if (f_asml != NULL)
  fprintf (f_asml, " add %%dx,%%ax\n");
 if (f_x86 != NULL)
  fprintf (f_x86, " .byte 0x01, 0xD0\n");
#ifdef INTERP
 *cp++ = code_add_r0_r1;
#endif
#ifdef COMPARM
 *cp++ = 0xE0800001;
#endif
#ifdef COMPX86
 *cp++ = 0x01;} *cp++ = 0xD0;
#endif
 return cp;
}

codeptr c_sub_r0_r1 (codeptr cp)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " sub ax,dx\n");
 if (f_asmi != NULL)
  fprintf (f_asmi, " sub %%ax,%%dx\n");
 if (f_asml != NULL)
  fprintf (f_asml, " sub %%dx,%%ax\n");
 if (f_x86 != NULL)
  fprintf (f_x86, " .byte 0x29, 0xD0\n");
#ifdef INTERP
 *cp++ = code_sub_r0_r1;
#endif
#ifdef COMPARM
 *cp++ = 0xE0400001;
#endif
#ifdef COMPX86
 *cp++ = 0x29;
 *cp++ = 0xD0;
#endif
 return cp;
}

codeptr c_mul_r0_r1 (codeptr cp)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " mul dx\n");
 if (f_asmi != NULL)
  fprintf (f_asmi, " mul %%dx\n");
 if (f_asml != NULL)
  fprintf (f_asml, " mul %%dx\n");
 if (f_x86 != NULL)
  fprintf (f_x86, " .byte 0xF7, 0xE2\n");
#ifdef INTERP
 *cp++ = code_mul_r0_r1;
#endif
#ifdef COMPARM
 *cp++ = 0xE0000091;
#endif
#ifdef COMPX86
 *cp++ = 0xF7;
 *cp++ = 0xE2;
#endif
 return cp;
}

codeptr c_bp_depl (codeptr cp, int depl)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " cmp ax,0\n jge %s\n", last_label);
 if (f_asmi != NULL)
  fprintf (f_asmi, " cmp %%ax,0\n jge %s\n", last_label);
 if (f_asml != NULL)
  fprintf (f_asml, " cmp %%ax,0\n jge %s\n", last_label);
 if (f_x86 != NULL)
  fprintf (f_x86, " .byte 0x3D, 0, 0\n jge %s\n", last_label);
#ifdef INTERP
 *cp++ = code_bp_depl;
 *cp++ = depl;
#endif
#ifdef COMPARM
 *cp++ = 0xE1B00000;
 *cp++ = 0x5A000000 + depl;
#endif
#ifdef COMPX86
 *cp++ = 0x3D;
 *cp++ = 0x00;
 *cp++ = 0x00;
 /* *cp++ = 0x2E; */

 *cp++ = 0x7D;
 *cp++ = depl;
/*
 *cp++ = 0x0F;
 *cp++ = 0x8D;
 *cp++ = depl & 0xFF;
 *cp++ = (depl & 0xFF00) >> 8;
*/
#endif
 return cp;
}

codeptr c_bz_depl (codeptr cp, int depl)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " cmp ax,0\n je %s\n", last_label);
 if (f_asmi != NULL)
  fprintf (f_asmi, " cmp %%ax,0\n je %s\n", last_label);
 if (f_asml != NULL)
  fprintf (f_asml, " cmp %%ax,0\n je %s\n", last_label);
 if (f_x86 != NULL)
  fprintf (f_x86, " .byte 0x3D, 0, 0\n je %s\n", last_label);
#ifdef INTERP
 *cp++ = code_bz_depl;
 *cp++ = (instr)depl;
#endif
#ifdef COMPARM
 *cp++ = 0xE1B00000;
 *cp++ = 0x0A000000 + depl;
#endif
#ifdef COMPX86
 *cp++ = 0x3D; /* cmp ax,0 */
 *cp++ = 0x00;
 *cp++ = 0x00;

 *cp++ = 0x74; /* je adr */
 *cp++ = (instr)depl;
#endif
 return cp;
}

codeptr c_setbradr (codeptr cp)
{
/* compile code to modify the instruction bp located at rA in such a way it
   branches to r0 */
 if (f_tasm != NULL)
  /* fprintf (f_tasm, " mov cx,ax\n sub cx,si\n sub cx,5\n mov [si+4],cx\n"); */
  fprintf (f_tasm, " mov cx,ax\n sub cx,si\n sub cx,5\n mov [byte ptr si+4],cl\n");
#ifdef INTERP
 *cp++ = code_setbradr;
#endif
#ifdef COMPARM
 *cp++ = 0xE040900A; /* R9=R0-RA */
 *cp++ = 0xE249900C; /* R9=R9-C */
 *cp++ = 0xE1A09149; /* R9=R9>>2 */

 *cp++ = 0xE59F7000; /* R7=[RF] */
 *cp++ = 0xEA000000; /* GOTO RF */
 *cp++ = 0xFFFFFF;
 *cp++ = 0xE0099007; /* R9=R9 and R7 */

 *cp++ = 0xE59A8004; /* R8=[RA+4] */
 *cp++ = 0xE59F7000; /* R7=[RF] */
 *cp++ = 0xEA000000; /* GOTO RF */
 *cp++ = 0xFF000000;
 *cp++ = 0xE0088007; /* R8=R8 and R7 */
 *cp++ = 0xE0888009; /* R8=R8+R9 */
 *cp++ = 0xE58A8004; /* [RA+4]=R8 */
 cp = compile_call (cp, (int(*)())f_dummyprint, 0, 0);
#endif
#ifdef COMPX86
 *cp++ = 0x89; *cp++ = 0xC1; /* MOV CX,AX */
 *cp++ = 0x29; *cp++ = 0xF1; /* SUB CX,SI */
 *cp++ = 0x83; *cp++ = 0xE9; *cp++ = 0x05; /* SUB CX,5 */
 *cp++ = 0x89; *cp++=0x4C; *cp++ = 0x04; /* MOV [SI+4],CX */
#endif
 return cp;
}

int label_tasm = 0;
int label_asmi = 0;
int label_asml = 0;

codeptr c_bp_ra (codeptr cp)
{
 if (f_tasm != NULL)
 {
  label_tasm++;
  fprintf (f_tasm, " cmp ax,0\n jl l%d\n jmp si\nl%d:\n",
   label_tasm, label_tasm);
 }
 if (f_asmi != NULL)
 {
  label_asmi++;
  fprintf (f_asmi, " cmp %%ax,0\n jl l%d\n jmp %%si\nl%d:\n",
   label_asmi, label_asmi);
 }
 if (f_asml != NULL)
 {
  label_asml++;
  fprintf (f_asml, " cmp %%ax,0\n jl l%d\n jmp *%%si\nl%d:\n",
   label_asml, label_asml);
 }
 if (f_x86 != NULL)
  fprintf (f_x86, " .byte 0x3D, 0, 0, 0x7C, 2, 0xFF, 0xE6\n");

#ifdef INTERP
 *cp++ = code_bp_ra;
#endif
#ifdef COMPARM
 *cp++ = 0xE1B00000;
 *cp++ = 0x51A0F00A;
#endif
#ifdef COMPX86
 *cp++ = 0x3D;      	/* cmp ax,0 */
 *cp++ = 0x00;
 *cp++ = 0x00;
 /* *cp++ = 0x2E; */
 *cp++ = 0x7C;      	/* jl $+2 */
 *cp++ = 0x02;
 *cp++ = 0xFF;        	/* jmp si */
 *cp++ = 0xE6;
#endif
 return cp;
}

codeptr c_bz_ra (codeptr cp)
{
 if (f_tasm != NULL)
 {
  label_tasm++;
  fprintf (f_tasm, " cmp ax,0\n jne l%d\n jmp si\nl%d:\n",
   label_tasm, label_tasm);
 }
 if (f_asmi != NULL)
 {
  label_asmi++;
  fprintf (f_asmi, " cmp %%ax,0\n jne l%d\n jmp %%si\nl%d:\n",
   label_asmi, label_asmi);
 }
 if (f_asml != NULL)
 {
  label_asml++;
  fprintf (f_asml, " cmp %%ax,0\n jne l%d\n jmp *%%si\nl%d:\n",
   label_asml, label_asml);
 }
 if (f_x86 != NULL)
  fprintf (f_x86, " .byte 0x3D, 0, 0, 0x75, 2, 0xFF, 0xE6\n");

#ifdef INTERP
 *cp++ = code_bp_ra;
#endif
#ifdef COMPARM
 *cp++ = 0xE1B00000;
 *cp++ = 0x01A0F00A;
#endif
#ifdef COMPX86
 *cp++ = 0x3D;      	/* cmp ax,0 */
 *cp++ = 0x00;
 *cp++ = 0x00;
 /* *cp++ = 0x2E; */
 *cp++ = 0x75;      	/* jne $+2 */
 *cp++ = 0x02;
 *cp++ = 0xFF;        	/* jmp si */
 *cp++ = 0xE6;
#endif
 return cp;
}

codeptr c_bz_r1 (codeptr cp)
{
#ifdef COMPARM
 *cp++ = 0xE1B00000;
 *cp++ = 0x01A0F001;
#endif
#ifdef COMPX86

#endif
 return cp;
}

codeptr c_call_depl (codeptr cp, int depl)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " call %s\n", last_label);
 if (f_asmi != NULL)
  fprintf (f_asmi, " call %s\n", last_label);
 if (f_asml != NULL)
  fprintf (f_asml, " call %s\n", last_label);
 if (f_x86 != NULL)
  fprintf (f_x86, " call %s\n", last_label);
#ifdef INTERP
 *cp++ = code_call_depl;
 *cp++ = depl;
#endif
#ifdef COMPARM
 *cp++ = 0xE1A0E00F;
 *cp++ = 0xEB000000 + depl;
#endif
#ifdef COMPX86
 *cp++ = 0x2E;
 *cp++ = 0xE8;
 *cp++ = depl;
 *cp++ = 0x00;
#endif
 return cp;
}

codeptr c_q_call_imr0 (codeptr cp)
{

}

codeptr c_call_ra (codeptr cp)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " call si\n");
 if (f_asmi != NULL)
  fprintf (f_asmi, " call %%si\n");
 if (f_asml != NULL)
  fprintf (f_asml, " call *%%si\n");
 if (f_x86 != NULL)
  fprintf (f_x86, " .byte 0xFF, 0xD6\n");
#ifdef INTERP
 *cp++ = code_call_ra;
#endif
#ifdef COMPARM
 *cp++ = 0xE1A0E00F;
 *cp++ = 0xE1A0F00A;
#endif
#ifdef COMPX86
 *cp++ = 0xFF;
 *cp++ = 0xD6;
#endif
 return cp;
}

/*
codeptr c_push_r0 (codeptr cp)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " push ax\n");
 if (f_asmi != NULL)
  fprintf (f_asmi, " push %%ax\n");
 if (f_asml != NULL)
  fprintf (f_asml, " push *%%ax\n");
 if (f_x86 != NULL)
  fprintf (f_x86, " .byte 0x50\n");
#ifdef INTERP
 *cp++ = code_push_r0;
#endif
#ifdef COMPARM

#endif
#ifdef COMPX86
 *cp++ = 0x50;
#endif
}

codeptr c_pop_r0 (codeptr cp)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " pop ax\n");
 if (f_asmi != NULL)
  fprintf (f_asmi, " pop %%ax\n");
 if (f_asml != NULL)
  fprintf (f_asml, " pop *%%ax\n");
 if (f_x86 != NULL)
  fprintf (f_x86, " .byte 0x58\n");
#ifdef INTERP
 *cp++ = code_pop_r0;
#endif
#ifdef COMPARM

#endif
#ifdef COMPX86
 *cp++ = 0x58;
#endif
}
*/

codeptr c_callext_ra (codeptr cp)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " call si\n");
 if (f_asmi != NULL)
  fprintf (f_asmi, " call %%si\n");
 if (f_asml != NULL)
  fprintf (f_asml, " call *%%si\n");
 if (f_x86 != NULL)
  fprintf (f_x86, " .byte 0xFF, 0xD6\n");
#ifdef INTERP
 *cp++ = code_callext_ra;
#endif
#ifdef COMPARM
 *cp++ = 0xE1A0E00F;
 *cp++ = 0xE1A0F00A;
#endif
#ifdef COMPX86
 *cp++ = 0xFF;
 *cp++ = 0xD6;
#endif
 return cp;
}

codeptr c_beginf (codeptr cp)
{
#ifdef INTERP
 *cp++ = code_beginf;
#endif
#ifdef COMPARM
 *cp++ = 0xE92D4000; /* PUSH RD RE */
#endif
 return cp;
}

codeptr c_endf (codeptr cp)
{
 if (f_tasm!=NULL)
  fprintf(f_tasm," ret\n");
#ifdef INTERP
 *cp++ = code_endf;
#endif
#ifdef COMPARM
 *cp++ = 0xE8BD8000; /* POP RD RF */
#endif
#ifdef COMPX86
 *cp++ = 0xC3;
#endif
 return cp;
}

codeptr c_ret (codeptr cp)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " ret\n");
 if (f_asmi != NULL)
  fprintf (f_asmi, " ret\n");
 if (f_asml != NULL)
  fprintf (f_asml, " ret\n");
 if (f_x86 != NULL)
  fprintf (f_x86, " .byte 0xC3\n");
#ifdef INTERP
 *cp++ = code_ret;
#endif
#ifdef COMPARM
 *cp++ = 0xE1A0F00E;
#endif
#ifdef COMPX86
 *cp++ = 0xC3;
#endif
 return cp;
}

codeptr c_ror_r0 (codeptr cp)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " ror ax,1\n");
 if (f_asmi != NULL)
  fprintf (f_asmi, " ror %%ax,1\n");
 if (f_asml != NULL)
  fprintf (f_asml, " ror %%ax,$1\n");
 if (f_x86 != NULL)
  fprintf (f_x86, " .byte 0xD1, 0xC8\n");
#ifdef INTERP
 *cp++ = code_ror_r0;
#endif
#ifdef COMPARM
 *cp++ = 0xE1A000A0;
#endif
#ifdef COMPX86
 *cp++ = 0xD1;
 *cp++ = 0xC8;
#endif
 return cp;
}

codeptr c_asr_r0 (codeptr cp)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " sar ax,1\n");
#ifdef INTERP
 *cp++ = code_asr_r0;
#endif
#ifdef COMPARM
 *cp++ = 0xE1A000C0;
#endif
#ifdef COMPX86
 *cp++ = 0xC1;
 *cp++ = 0xF8;
 *cp++ = 0x01;
#endif
 return cp;
}


codeptr c_and_r0_r1 (codeptr cp)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " and ax,dx\n");
 if (f_asmi != NULL)
  fprintf (f_asmi, " and %%ax,%%dx\n");
 if (f_asml != NULL)
  fprintf (f_asml, " and %%ax,%%dx\n");
 if (f_x86 != NULL)
  fprintf (f_x86, " .byte 0x21, 0xD0\n");
#ifdef INTERP
 *cp++ = code_and_r0_r1;
#endif
#ifdef COMPARM
 *cp++ = 0xE0000001;
#endif
#ifdef COMPX86
 *cp++ = 0x21;
 *cp++ = 0xD0;
#endif
 return cp;
}

codeptr c_xor_r0_r1 (codeptr cp)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " xor ax,dx\n");
 if (f_asmi != NULL)
  fprintf (f_asmi, " xor %%ax,%%dx\n");
 if (f_asml != NULL)
  fprintf (f_asml, " xor %%ax,%%dx\n");
 if (f_x86 != NULL)
  fprintf (f_x86, " .byte 0x31, 0xD0\n");
#ifdef INTERP
 *cp++ = code_xor_r0_r1;
#endif
#ifdef COMPARM
 *cp++ = 0xE0200001;
#endif
#ifdef COMPX86
 *cp++ = 0x31;
 *cp++ = 0xD0;
#endif
 return cp;
}

int f_exit (void)
{
 exit(0);
}

codeptr c_exit (codeptr cp)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " mov ax,0\n int 21h\n");
#ifdef INTERP
 *cp++ = code_exit;
#endif
#ifdef COMPARM
 cp = compile_call0 (cp, f_exit);
#endif
#ifdef COMPX86
 *cp++ = 0xB8; *cp++ = 0; *cp++ = 0; /* mov ax,0 */
 *cp++ = 0xCD; *cp++ = 0x21; /* int 21h */
#endif
 return cp;
}

any fillmem;
#ifdef LINUXCOMP
instr *fillmem_code;
#else
instr fillmem_code[1000];
#endif

void clearcache(void)
{
#ifdef LINUXCOMP
 __clear_cache((char *)cod, (char *)(cod+CODESIZE));
 __clear_cache((char *)fillmem_code, (char *)(fillmem_code+1000));
#endif
}


codeptr lengthadr;

int ncode=0;

codeptr c_code (codeptr cp)
{
 /*
  to do : produce code for f_tasm
  problem : length unknown
  possible solution : write code to buffer until length known,
  then write length and buffer to file
 */
 ncode++;
 if (f_tasm!=NULL)
 {
  /* fprintf(f_tasm," call _fillmem\n"); */
  /* asm_call_ext ("fillmem"); */
  fprintf (f_tasm, " lea bp,_fillmem\n call bp\n");
  fprintf(f_tasm," db b%d-a%d\na%d:\n",
    ncode, ncode, ncode);
 }
#ifdef INTERP
 *cp++ = code_fillmem;
 lengthadr = cp;
 *cp++ = 0;
#else
 /* cp = compile_call0 (cp, fillmem.intf);
 */

 *cp++ = 0xE28FE004; /* RE=RF+4 */
 *cp++ = 0xE51FF004; /* RF=[RF-4] */
 *cp++ = fillmem.ins;
 lengthadr = cp;
 *cp++ = 0;
#endif
 return cp;
}

codeptr c_endcode (codeptr cp)
{
int n;
 if (f_tasm!=NULL)
  fprintf (f_tasm, "b%d:\n", ncode);
 n = cp - lengthadr - 1;
 *lengthadr = (instr)n;

 return cp;
}

codeptr c_dumpcode (codeptr cp)
{
 /* dmpcode(); */
 if (f_tasm != NULL)
 {
  asm_call_ext("dmpcode");
 }
#ifdef INTERP
 *cp++ = code_dumpcode;
#else
 cp = compile_call (cp, (int(*)())dmpcode, 0, 0);
#endif
 return cp;
}

void initcvm (void)
{
}

codeptr c_initcvm (codeptr cp)
{
 if (f_tasm != NULL)
  asm_call_ext ("initcvm");
#ifdef INTERP
 *cp++ = code_initcvm;
#else
 cp = compile_call (cp, (int(*)())initcvm, 0, 0);
#endif
 return cp;
}

codeptr c_intbios (codeptr cp, int intnum)
{
 if (f_tasm != NULL)
  fprintf (f_tasm, " int 0%Xh\n", intnum);
#ifdef INTERP
 *cp++ = code_intbios;
 *cp++ = (instr)intnum;
#endif
 return cp;
}

void init_code (void)
{
codeptr cp, cp1;
char bufasm[100];
#ifdef LINUXCOMP
 fillmem_code = mmap (NULL, 4000,
  PROT_READ | PROT_WRITE | PROT_EXEC,
  MAP_PRIVATE | MAP_ANONYMOUS,
  -1, 0);
 if (fillmem_code == MAP_FAILED)
 {
  printf ("mmap failed\n");
  perror("mmap");
  exit(0);
 }
#endif
 fillmem.cp = fillmem_code;
 cp = fillmem_code;
#ifdef COMPARM
 *cp++ = 0xE92D0003; /* PUSH RD 3 */
 /* *cp++ = 0xE28EE004; RE=RE+4 */
 *cp++ = 0xE59E0000; /* R0=[RE] */
 *cp++ = 0xE28EE004; /* RE=RE+4 */
 *cp++ = 0xE2400001; /* loop: R0=R0-1 */
 *cp++ = 0xE1B00000; /* R0?=R0 */
 *cp++ = 0xBA000004; /* <0 GOTO fin (+4) */
 *cp++ = 0xE59E1000; /* R1=[RE] */
 *cp++ = 0xE28EE004; /* RE=RE+4 */
 *cp++ = 0xE58C1000; /* [RC]=R1 */
 *cp++ = 0xE28CC004; /* RC=RC+4 */
 *cp++ = 0xEAFFFFF7; /* GOTO loop (-9) */
 *cp++ = 0xE8BD0003; /* fin: POP RD 3 */
 *cp++ = 0xE1A0F00E; /* RF=RE */
#endif
#ifdef COMPX86
 *cp++ = 0x53; /* PUSH BX */
 *cp++ = 0x51; /* PUSH CX */
 *cp++ = 0x56; /* PUSH SI */
 *cp++ = 0x89; *cp++ = 0xE3; /* MOV BX,SP */
 *cp++ = 0x8B; *cp++ = 0x77; *cp++ = 0x06; /* MOV SI,[BX+6] */
 *cp++ = 0x8A; *cp++ = 0x0C; /* MOV CL,[SI] */
 *cp++ = 0xB5; *cp++ = 0x00; /* MOV CH,0 */
 *cp++ = 0x46; /* INC SI */
 *cp++ = 0xFC; /* CLD */
 *cp++ = 0xF3; *cp++ = 0xA4; /* REP MOVSB */
 *cp++ = 0x89; *cp++ = 0x77; *cp++ = 0x06; /* MOV [BX+6],SI */
 *cp++ = 0x5E; /* POP SI */
 *cp++ = 0x59; /* POP CX */
 *cp++ = 0x5B; /* POP BX */
 *cp++ = 0xC3; /* RET */
#endif
#ifdef COMPARM
#ifdef TRACE
 for (cp1=fillmem.cp; cp1<cp; cp1++)
 {
  printasm (bufasm, (unsigned int)(cp1[0]), (unsigned int)(cp1));
  printf ("%8X: %08lX %s\n", cp1, cp1[0], bufasm);
 }
 gets (bufasm);
#endif
#endif
}

codeptr gcp;

void dmpcode (void)
{
 char buf[1000];
 char bufasm[300];
 codeptr cp;
 int i;
 any ucode;

 cp=gcp;
 ucode.cp=cod;

 printf ("Machine code:\n");
#ifdef INTERP
 for (i=0; i<cp-cod; i++)
 { 
  if (i%16 == 0)
   gets(buf);
  printf ("%3X: %X: %08lX %s\n", 
   i, cod+i, cod[i], instr_name(cod[i]));
 }
 gets(buf);
#else

 for (i=0; i<gcp-cod; i++)
 {
#ifdef COMPARM
  printasm (bufasm, (unsigned int)(ucode.cp[i]), (unsigned int)(ucode.cp+i));
  /* printf ("%8X: %08lX %s\n", ucode.cp+i, ucode.cp[i], bufasm); */
  printf ("%X %08lX %c%c%c%c %s\n",
   ucode.cp+i, ucode.cp[i], 
   ucode.cp[i]>>24,
   ucode.cp[i]>>16,
   ucode.cp[i]>>8,
   ucode.cp[i],
   bufasm);
  if (i%16==15) gets(buf);
#else
  if (i%8 == 0)
   printf ("\n%3X: ", i);
  printf ("%02X ", cod[i]);
#endif
 }
 printf ("\n");
#endif
}


void dmpcodeadrlen (int adr, int len)
{
 char buf[1000];
 char bufasm[300];
 codeptr cp;
 int i;
 any ucode;
 codeptr bgn;

 bgn = (codeptr)adr;

 cp=gcp;
 ucode.cp=cod;

 printf ("Machine code:\n");
#ifdef INTERP
 for (i=0; i<len; i++)
 { 
  if (i%16 == 0)
  {
   printf ("...");
   gets(buf);
  }
  printf ("%3X: %X: %08lX %s\n", 
   i, bgn+i, bgn[i], instr_name(bgn[i]));
 }
 printf ("End...");
 gets(buf);
#else

 for (i=0; i<gcp-cod; i++)
 {
#ifdef COMPARM
  printasm (bufasm, (unsigned int)(ucode.cp[i]), (unsigned int)(ucode.cp+i));
  /* printf ("%8X: %08lX %s\n", ucode.cp+i, ucode.cp[i], bufasm); */

  printf ("%X %08lX %c%c%c%c %s\n",
   ucode.cp+i, ucode.cp[i], 
   ucode.cp[i]>>24,
   ucode.cp[i]>>16,
   ucode.cp[i]>>8,
   ucode.cp[i],
   bufasm);

  if (i%16==15) gets(buf);
#else
  if (i%8 == 0)
   printf ("\n%3X: ", i);
  printf ("%02X ", cod[i]);
#endif
 }
 printf ("\n");
#endif
 printf ("\nEnd of code dump\n");
}

char mode;

#ifdef JNI

int initialized = 0 ; 

char codecopy[10000];
char *codecopyend;

void interp_debug (char, int);

void copycode (void)
{
 union
 {
  char *p;
  void (*f) (char, int);
 } u;
 char *q;
 u.f = interp_debug;
 q = codecopy;
 while (u.f <= interp)
 {
  *q++ = *(u.p)++;
 } 
 codecopyend = q;
}

void checkcode (void)
{
 union
 {
  char *p;
  void (*f) (char, int);
 } u;
 char *q;
 u.f = interp_debug;
 q = codecopy;
 while (u.f <= interp)
 {
  if (*q != *(u.p))
  {
   sprintf (buf, "program modified %X %X %X %X", q, *q, u.p, *(u.p));
   printf ("%s\n", buf);
   trace1(buf);
   exit(0);
  }
  q++;
  u.p++;
 }
}

void initialize (void)
{
 any ucode;
 int i; 
 codeptr cp ;
 char bufasm [300] ; 
 char buf [1000] ;  
  copycode () ; 
  trace("init...");
  
  init() ;
  trace("init done");
  ucode.cp = cod ; 
  
  printf ("First pass...\n");
  trace ("First pass...");
  cp = compile_file (cod, "/mnt/sdcard/forth.cvm", NULL, NULL, NULL, NULL) ; 
  lastword = NULL ; 
  gnw = 0 ; 
  printf ("Second pass...\n");
  trace ("Second pass...");
  cp = compile_file (cod, "/mnt/sdcard/forth.cvm", NULL, NULL, NULL, NULL) ; 

  gcp = cp ; 
  printf ("Initialized.\n");
  trace ("Initialized.\n");
}

void cvm (int first) 
{
 any ucode;
 int i; 
 codeptr cp ;
 char bufasm [300] ; 
 char buf [1000] ;  

 copycode () ; 
 printf ("Running...\n");
 trace ("Running...");
 interp(first) ; 
 trace ("Done.");
 printf ("Done.\n");
} 

#else
int main (int argc, char *argv[])
{
any ucode;
int i;
codeptr cp;
char bufasm[300];
char buf[1000];
 /* printf ("%X\n",asm_call_ext); */
 /* printf ("\n#0\n"); */
 init ();
 ucode.cp = cod;
/*
#ifdef PPC
 printf ("First pass\n");
 cp = compile_file (cod, "\\pgcc\\samp\\cvm\\test3.txt", NULL, NULL, NULL, NULL);
 printf ("Second pass\n");
 cp = compile_file (cod, "\\pgcc\\samp\\cvm\\test3.txt",
  "\\pgcc\\samp\\cvm\\test3.asm",
  "\\pgcc\\samp\\cvm\\test3i.s",
  "\\pgcc\\samp\\cvm\\test3.s",
  "\\pgcc\\samp\\cvm\\test3x.s");
 printf ("Done\n");
#else
 printf ("First pass\n");
 cp = compile_file (cod, "test3.txt", NULL, NULL, NULL, NULL);
 printf ("Second pass\n");
 cp = compile_file (cod,
  "test3.txt",
  "test3.asm",
  "test3i.s",
  "test3.s",
  "test3x.s");
 printf ("Done\n");
#endif
*/

#ifdef PPC
 printf ("First pass\n");
 cp = compile_file (cod, "cvm.txt", NULL, NULL, NULL, NULL);
 printf ("Program size: %u = 0x%X instructions\n", cp-cod, cp-cod);

 lastword = NULL;
 gnw = 0;

 printf ("Second pass\n");
 cp = compile_file (cod, "cvm.txt", "cvm.asm", NULL, NULL, NULL);
 printf ("Done\n");
#else
 /*printf("argc=%X\n",argc);*/

 printf ("file %s\n",argv[2]);

 printf ("First pass\n");
 cp = compile_file (cod, argv[2], NULL, NULL, NULL, NULL);
 printf ("Program size: %u = 0x%X instructions\n", cp-cod, cp-cod);

 lastword = NULL;
 gnw = 0;

 printf ("Second pass\n");
 if (argc >= 3)
  cp = compile_file (cod, argv[2], argv[3], NULL, NULL, NULL);
 else
  cp = compile_file (cod, argv[2], NULL, NULL, NULL, NULL);
 printf ("Done\n");
#endif

 /* cp = compile_prog (cod); */

 gcp=cp;

#ifdef TRACE
 printf ("Machine code:\n");
#ifdef INTERP
 for (i=0; i<cp-cod; i++) 
  printf ("%3X: %lX: %08lX %s\n", i, cod+i, cod[i], instr_name(cod[i]));
 gets(buf);
#else

 for (i=0; i<cp-cod; i++)
 {
#ifdef COMPARM
  printasm (bufasm, (unsigned int)(ucode.cp[i]), (unsigned int)(ucode.cp+i));
  /* printf ("%8X: %08lX %s\n", ucode.cp+i, ucode.cp[i], bufasm);*/
  printf("%X %08lX %c%c%c%c %s\n",
   ucode.cp+i,
   ucode.cp[i],
   ucode.cp[i],
   ucode.cp[i]>>8,
   ucode.cp[i]>>16,
   ucode.cp[i]>>24,
   bufasm);
  /* if (i%16==15) gets(buf);*/
#else
  if (i%8 == 0)
   printf ("\n%3X: ", i);
  printf ("%02X ", cod[i]);
#endif
 }
 printf ("\n");
#endif
#endif

#ifndef PPC
 if (argv[1][0] == 'r' || argv[1][0] == 'd' || argv[1][0] == 't')
#endif
 {
#ifdef INTERP
#ifdef PPC
 char buf[1000];
 printf("debug?");
 gets(buf);
 mode = *buf;
 if (mode == 0)
  mode = 'r';
 if (mode == 'n')
  mode = 'r';
 if (mode == 'y')
  mode = 'd';
 if(mode != 'r')
 {
  printf ("Running with debugging\n");
  debug();
 }
 else
 {
  printf ("Running without debugging\n");
  interp(1);
 }
#else
  mode = argv[1][0];
  if (argv[1][0] == 'r' )
   interp (1);
  else
   debug ();
#endif
#else
  clearcache();
#ifdef PPC
  (*(ucode.f1))(1);
#else
  (*(ucode.f))(1);
#endif
#endif
 }

#ifdef TRACE
 for (i=0; i<cp-cod; i++)
 {
#ifdef COMPARM
  printasm (bufasm, (unsigned int)(ucode.cp[i]), (unsigned int)(ucode.cp+i));
  printf ("%8X: %08lX %s\n", ucode.cp+i, ucode.cp[i], bufasm);
 /* if (i%16==15) gets(buf); */
#else
  if (i%8 == 0)
   printf ("\n%3X: ", i);
  printf ("%02X ", cod[i]);
#endif
 }
#endif

 return 0;

#if 0
 gets(buf);
 printf("\n#1\n");
 ucode.cp = cod;
 printf("\n#2\n");
 cp = compile_prog (cod);
 printf("\n#3\n");
 for (i=0; i<=cp-cod; i++)
 {
#ifdef COMPARM
  printasm (bufasm, (unsigned int)(ucode.cp[i]), (unsigned int)(ucode.cp+i));
#else
  bufasm[0] = 0;
#endif
  printf ("%X: %08lX %s\n", ucode.cp+i, ucode.cp[i], bufasm);
  if (i%16==15) gets(buf);
 }
 printf("\n#4\n");

#ifdef INTERP
 interp();
#else
 clearcache();
 (*(ucode.f))();
#endif
 printf("\n#5\n");
#endif
}

#endif 
