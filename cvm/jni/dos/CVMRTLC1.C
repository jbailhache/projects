#define COMPX86

void test (void);

start ()
{
 test();
 myexit();
}

main()
{
 test();
}

void printhex (int x);

int scanhex (void)
{
 int x;
 char c;
 x = 0;
 for (;;)
 {
  /*
  myputchar('<');
  printhex(x);
  myputchar('>');
  */
  c = mygetchar();
  if (c>='0' && c<='9')
   x = (x<<4) + c - '0';
  else if (c>='A' && c<='F')
   x = (x<<4) + c - 'A' + 0xA;
  else
   break;
 }
 return x;
}

void printhex (int x)
{
 int d, i;
 for (i=0; i<4; i++)
 {
  d = ((x << (i*4)) >> 12) & 0xF;
  if (d <= 9)
   myputchar ('0'+d);
  else
   myputchar ('A'+d-0xA);
 }
}

#define NULL ((void *) 0)

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

struct word
{
 struct word *link;
 any code;
 any param;
 chr *pname;
 chr name[4];
};

typedef struct word *pword;

pword lastword = (pword)0;

#define DICSIZE 1000
int dic[DICSIZE];

any freedic;
any freespace;

pword gpw;
int gwri;

codeptr c_mov_ra_im (codeptr cp, int im, char *l);
codeptr c_mov_r0_cont_ra (codeptr cp);
codeptr c_mov_ra_cont_ra (codeptr cp);

void init_dic (void)
{
 freedic.pw = (pword)dic;
}

chr getchr1 ()
{
 chr c;
 c = mygetchar();
 /* lastcp = instbl+c; */
 return c;
}

chr (*pgetchr) (void) = getchr1;

#define getchr (*pgetchr)

void putchr (chr c)
{
 myputchar(c);
}

#define WORDSIZE 32

chr cr;
chr wr[WORDSIZE];
char awr[WORDSIZE];

chr readcarac (void)
{
 cr = getchr();
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

int mystrlen (char *s)
{
 int i;
 for(i=0; ;i++)
  if(s[i]==0)
   return i;
}

void mystrcpy (char *dst, char *src)
{
 int i;
 for(i=0;src[i];i++)
  dst[i]=src[i];
}

int mystrcmp (char *s1, char *s2)
{
 int i;
 for(i=0;;i++)
 {
  if (s1[i]==0)
  {
   if (s2[i]==0)
    return 0;
   else
    return i+1;
  }
  else if (s2[i]==0)
   return i+1;
  else if (s1[i]!=s2[i])
   return i+1;
 }
}

void readword (void)
{
	int i;
	readcarac();
	/* TRACE "readword: 1st cr = '%c' %X\n", cr, cr ENDTRACE */
	while (isblnk (cr))
	{
		readcarac();
		/* TRACE "skip blanks: cr = '%c' %X\n", cr, cr ENDTRACE */
	}
	i = 0;
	while (iswordcarac(cr))
	{
		/* TRACE "read cr = '%c' %X\n", cr, cr ENDTRACE */
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
}

void testreadword (void)
{
 for (;;)
 {
  readword();
  printf (" <%s> ", wr);
  if (!mystrcmp((char*)wr,"BYE"))
   break;
 }
}

/* pword lastword; */

int slen (chr *s)
{
 return mystrlen((char *)s);
}

int scmp (chr *s1, chr *s2)
{
 return mystrcmp ((char*)s1, (char*)s2);
}

chr * scpy (chr *s1, chr *s2)
{
/* return (chr*) mystrcpy ((char*)s1, (char*)s2); */
 int i;
 for (i=0; s2[i]; i++)
  s1[i]=s2[i];
 return s1;
}

codeptr compile_pushint (codeptr cp, int x);

pword findword (chr *name)
{
	pword pw;
	char buf[100];
	int i;
	/* TRACE "begin findword\n" ENDTRACE */
	for (i=0; name[i]; i++)
		buf[i]=name[i];
	buf[i]=0;
	/* TRACE "findword <%s>\n", buf ENDTRACE */
	pw = lastword;
	/* TRACE "loop\n" ENDTRACE */
	for (;;)
	{
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
	return lastword;
}

pword getwordstr (chr *name)
{
	pword pw;
	char aname[WORDSIZE];
	int i;
	for (i=0; name[i]; i++)
		aname[i]=name[i];
	aname[i]=0;
	/* TRACE "getword <%s>\n", aname ENDTRACE */
	pw = findword (name);
	/* TRACE "pw = %X\n", pw ENDTRACE */
	if (pw != NULL)
	{
		/* TRACE "getword: found\n" ENDTRACE */
		return pw;
	}
	/* TRACE "getword: not found\n" ENDTRACE */
	pw = createword (name);
	/* TRACE "pw=%X\n", pw ENDTRACE */
	/* TRACE "end getword\n" ENDTRACE */
        gpw = pw;
	return pw;
}

pword getword (void)
{
 readword();
 return getwordstr(wr);
}


void test (void)
{
 int x;
 printhex (0x1A2B);
 x = scanhex();
 x = x+1;
 printhex(x);
}

