
// #include <windows.h>
// #include <windowsx.h>
// #include <aygshell.h>

// #include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>

#define TRACES

#ifdef TRACES
#define TRACE fprintf (ftrace, "lastword=%X freespace=%X out.f=%X out.p=%X ", lastword,freespace.i, out.f, out.p); fprintf (ftrace,
#define ENDTRACE ); fflush(ftrace); 
#endif

typedef wchar_t carac;
#define WORDSIZE 200
typedef unsigned int instr;

typedef union
{
	int i;
	int *pi;
	struct header *ph;
	int (*fi) ();
	instr * (*f) ();
	instr *pcode;
	char *pchar;
	carac *pcarac;
	FILE *fd;
	instr instruc;
} any;

typedef struct header
{
	struct header *link;
	any value;
	any param;
	int wmode;
	struct header *ph;
	any imvalue;
	int length;
	carac name[2];
} *pheader;


typedef struct fp
{
	int (*f) ();
	any p;
} fp;

#ifdef WMFORTH
#define DATA extern
#else 
#define DATA  
#endif

DATA fp out;

DATA struct
{
	int mode;
	carac curchar;
	carac curword[WORDSIZE];
	carac *inptr, *outptr;
	int inlevel;
	// FILE *out1;
	// instr *ptrcode;
	int level;
	// any startcode;
	pheader lastword;
	any freespace;
	int *ptrstack;
	int *ptrpstack;
	int iflevel;
	int wlevel;

	int *dic;
	instr *codes;
	instr **ptrcodes;
	carac *wr;
	char *awr;
	fp *instack;
	any *startcodes;
	pheader phcalled;
} globals;


#define mode (globals.mode)
#define inptr (globals.inptr)
#define outptr (globals.outptr)
#define inlevel (globals.inlevel)
// #define out1 (globals.out1)
// #define ptrcode (globals.ptrcode)
#define level (globals.level)
// #define startcode (globals.startcode)
#define lastword (globals.lastword)
#define freespace (globals.freespace)
#define ptrstack (globals.ptrstack)
#define ptrpstack (globals.ptrpstack)
#define iflevel (globals.iflevel)
#define wlevel (globals.wlevel)
#define phcalled (globals.phcalled)

#define NLABELS 0x2000
#define LEN 0x20
extern struct
{
	char name[LEN];
	unsigned int value;
} labels[NLABELS];
DATA int nl;

int dasm = 1;

/*
struct
{
	int adr;
	char *name;
} tabadr[1000];

int nadr = 0;
*/

#define LEN 0x20

DATA struct
{
	// unsigned int adr;
	char name[LEN];
	unsigned int adr;
} *tabadr;

// DATA int nl;
#define nadr nl

DATA FILE *ftrace;

/*** assembleur ***/

int match (unsigned int x, unsigned int pattern, unsigned int mask)
{
	return ((x & mask) == (pattern & mask));
}


int isd (char c)
{
	if (c>= '0' && c <= '9')
		return 1;
	if (c>='A' && c<='F')
		return 1;
	return 0;
}

unsigned int instrcode (char *opcode, int nargs, unsigned int args[], char *com, int adr)
{
	unsigned int x; int depl;
	int i;

	/*
	fprintf (out1, "instrcode %X : <%s> ", adr, opcode);
	for (i=0; i<nargs; i++)
		fprintf (out1, "%X ", args[i]);
	fprintf (out1, "\n");
	*/

	if (!strcmp (opcode, "PUSHR") || !strcmp (opcode, "PUSHR,"))
	{
		x = 0x9200000 | 0x10000 * args[0] | args[1];
		// fprintf (out1, "%X %X %X\n", args[0], 0x92D0000 | args[0], x);
	}
	else if (!strcmp (opcode, "POPR") || !strcmp (opcode, "POPR,"))
		x = 0x8B00000 | 0x10000 * args[0] | args[1];
	else if (!strcmp (opcode, "R=R"))
		x = 0x1A00000 | 0x1000 * args[0] | args[1];
	else if (!strcmp (opcode, "R=") && args[1]<0x100)
		x = 0x3A00000 | 0x1000 * args[0] | args[1];
	else if (!strcmp (opcode, "R=R+R"))
		x = 0x0800000 | 0x1000 * args[0] | 0x10000 * args[1] | args[2];
	else if (!strcmp (opcode, "R=R*R"))
		x = 0x0000090 | args[0] * 0x10000 | args[1] * 0x100 | args[2];
	else if (!strcmp (opcode, "R=R|R"))
		x = 0x1800000 | args[1] << 16 | args[0] << 12 | args[2];
	else if (!strcmp (opcode, "R=R+") && args[2] < 0x100)
		x = 0x2800000 | args[1] << 16 | args[0] << 12 | args[2];
	else if (!strcmp (opcode, "R=R-") && args[2] < 0x100)
		x = 0x2400000 | args[1] << 16 | args[0] << 12 | args[2];
	else if (!strcmp (opcode, "R=R|") && args[2] < 0x100)
		x = 0x3800000 | args[1] << 16 | args[0] << 12 | args[2];
	else if (!strcmp (opcode, "R=R->~") && args[2] < 0x100)
		x = 0x3E00000 | args[1] << 16 | args[0] << 12 | args[2];
	else if (!strcmp (opcode, "?=?-"))
		x = 0x1500000 | 0x1000 * args[0] | 0x10000 * args[1] | args[2];
	else if (!strcmp (opcode, "GOTO"))
	{
		depl = ((args[0] - (adr + 8)) >> 2) & 0xFFFFFF;
		x = 0xA000000 | depl;
	}
	else if (!strcmp (opcode, "()"))
	{
		depl = ((args[0] - (adr + 8)) >> 2) & 0xFFFFFF;
		x = 0xB000000 | depl;
	}
	else if (!strcmp (opcode, "R=[]"))
	{
		depl = (args[1] - (adr + 8)) & 0xFFF;
		x = 0x59F0000 | 0x1000 * args[0] | depl;
	}
	else if (!strcmp (opcode, "[]=R"))
	{
		depl = (args[0] - (adr + 8)) & 0xFFF;
		x = 0x58F0000 | 0x1000 * args[0] | depl;
	}
	else if (!strcmp (opcode, "R=[R+]"))
		x = 0x5900000 | 0x10000 * args[1] | 0x1000 * args[0] | args[2];
	else if (!strcmp (opcode, "[R+]=R"))
		x = 0x5800000 | 0x10000 * args[0] | 0x1000 * args[2] | args[1];

	else if (!strcmp (opcode, "[R+R<<]=R"))
		x = 0x7800000 | args[0] << 16 | args[3] << 12 | args[2] << 7 | args[1];

	else if (!strcmp (opcode, "RR#?=[R+]"))
		x = 0x8D00000 | args[1] << 16 | args[0];
	else if (!strcmp (opcode, "RR#=[R+]"))
		x = 0x8900000 | args[1] << 16 | args[0];
	else if (!strcmp (opcode, "[R+]?=RR#"))
		x = 0x8C00000 | args[0] << 16 | args[1];

	else if (!strcmp (opcode, "R=+$[R+R]"))
		x = 0x19000D0 | args[1] << 16 | args[0] << 12 | args[2];
	else if (!strcmp (opcode, "+$[R+R]=R"))
		x = 0x18000D0 | args[0] << 16 | args[2] << 12 | args[1];
 
	else
		sscanf (com, "%X", &x);
	// fprintf (out1, "instrcode = %07X\n", x);
	return x;
}

int asmbl (char *line, int adr)
{
	int lab, ch, d, i, k, adr1, call;
	unsigned int x, x1;
	char *com;
	union
	{
		int adr;
		char *pchar;
		unsigned int *puint;
	} u;
	char *cond[] = { "==", "!=", "c", "!c", "<0", ">=0",  "OVF", "!OVF", "HI", "LS", ">=", "<", ">", "<=", "", "UNC" };

	// fprintf (out1, "asm %X <%s>\n", adr, line);

	adr1 = adr;
	call = 0;

	d = 0;
	lab = 0;
	ch = 0;
	for (i=0; line[i]; i++)
	{
		if (line[i] == ':')
		{
			lab = 1;
			d = i+1;
		}
		if (line[i] == '"')
			ch = 1;
	}

	// fprintf (out1, "lab=%d ch=%d d=%d\n", lab, ch, d);

	if (ch)
	{
		// fprintf (out1,"ch\n");
		for (i=d; line[i]!='"'; i++);
		for (k=i+1; line[k]!='"' && line[k]!=0; k++)
		{
			u.adr = adr++;
			*(u.pchar) = line[k];
		}
		u.adr = adr++;
		*(u.pchar) = 0;
		while (adr % 4)
		{
			u.adr = adr++;
			*(u.pchar) = 0;
		}
	}
	else
	{
		char op[LEN], condi[LEN];
		int condcode;
		char *opcode;
		int lop;
		char args[8][10];
		unsigned int argsn[8];
		int nargs, larg, i, k;
		// fprintf (out1,"non ch\n");
		nargs = 0;
		lop = 0;
		larg = 0;
		// fprintf (out1, "avant boucle\n");
		for (i=d; line[i]!=0 && line[i]!='\n' && line[i]!='\r' && line[i]!='%'; i++)
		{
			if (line[i] != ' ' && line[i]!='\t')
			{
				if (isd(line[i]))
				{
					for (k=0; isd(line[i+k]); k++)
						args[nargs][k] = line[i+k];
					args[nargs][k] = 0;
					nargs++;
					i += k-1;
				}
				else
				{
					op[lop++] = line[i];
				}
			}
		}
		op[lop] = 0;
		// fprintf (out1, "op=<%s> %d args\n", op, nargs);

		if (line[i]=='%')
			com = line+i+1;
		else 
			com = "BADC0DE";

		for (i=0; i<nargs; i++)
		{
			sscanf (args[i], "%X", &(argsn[i]));
			// fprintf (out1, "%d <%s> %X\n", i, args[i], argsn[i]);
		}

		opcode = op;
		strcpy (condi, "");
		condcode = 14;

		for (k=0; k<14; k++)
			if (!strncmp (op, cond[k], strlen(cond[k])))
			{
				strcpy (condi, cond[k]);
				condcode = k;
				opcode = op + strlen(cond[k]);
			}
		
		/*
		fprintf (out1,"<cond:%s:%d><%s>", condi, condcode, opcode);
		for (k=0; k<nargs; k++)
			fprintf (out1, "<%d:%s>", k, args[k]);
		fprintf (out1, "\n");
		*/

		u.adr = adr;
		
		// fprintf (out1, "test opcode\n");
		if (!*opcode)
		{
			// fprintf (out1, "opcode vide\n");
			sscanf (args[0], "%X", &x);
			// fprintf (out1, "arg=%X\n", x);
			*(u.puint) = x;
			// fprintf (out1, "fin cas opcode vide\n");
			adr += 4;
		}		
		else if (!strcmp (opcode, "RS"))
		{
			adr += argsn[0];
		}
		else
		{
			// fprintf (out1, "opcode non vide\n");
			// x = 0;
			x = instrcode (opcode, nargs, argsn, com, adr) | condcode * 0x10000000;
			// fprintf (out1, "ecriture code %X %X %X\n", adr, u.puint, x);
			*(u.puint) = x;
			// fprintf (out1, "fin cas opcode non vide\n");
			adr += 4;
		}

		sscanf (com, "%X", &x1);
		/*
		 fprintf (out1, "%X: %X", adr1, x);
		if (x != x1 && !match (x, 0xB000000, 0xF000000))
			fprintf (out1, " *** different ***");
		fprintf (out1, "\n\n");
		*/
		
	}
	// fprintf (out1, "fin asm\n");
	return adr;


}

int codeasm (char *s, int adr)
{
	unsigned int code1 [16];
	asmbl(s, (int)code1);
	return code1[0];
}

char str[1000];

void substlabels (char *line, char *line1)
{
	int i, k, l, trouve;
	int ad;
	i = 0;
	k = 0;
	TRACE "substlabels <%s> nl=%d\n", line, nl ENDTRACE
	for (;;)
	{
		if (line[i] == 0)
		{
			line1[k] = 0;
			break;
		}
		trouve = 0;
		for (l=0; l<nl; l++)
		{
			// fprintf (out1, "%d %d %d <%s> <%s>\n", i, k, l, labels[l].name, line+i);
			if (!strncmp (line+i, labels[l].name, strlen(labels[l].name)))
			{
				trouve = 1;
				sprintf (str, "pos %d %d label %d <%s>=%X\n", i, k, l, labels[l].name, labels[l].value);
				i += strlen (labels[l].name);
				ad = 0;
				if (line[i] == '+')
				{
					sscanf (line+i+1, "%X", &ad);
					i++;
					while ((line[i] >= '0' && line[i] <= '9') || (line[i] >= 'A' && line[i] <= 'F'))
						i++;
				}	
				k += sprintf (line1+k, "%X", labels[l].value+ad);
				break;
			}
		}
		if (!trouve)
			line1[k++] = line[i++];
	}
	// fprintf (out1, "%s\n%s\n", line, line1); 
}


FILE *out1;
DATA wchar_t exename[] = L"ProgramName";
DATA char exenamea[] = "ProgramName";
int adr;
unsigned int *code;

#ifdef WINDOWS

int callcode (FILE *fd, HINSTANCE hInstance, HINSTANCE hPrevInstance, LPWSTR lpszCmdLine, int nCmdShow)
{
	int r;
	union
	{
		unsigned int *ptr;
		int (*f) ();
	} u;
	u.ptr = code;
	// fprintf (out1, "appel code...\n");
	r = (*(u.f))(fd, hInstance, hPrevInstance, lpszCmdLine, nCmdShow);
	// fprintf (out1, "resultat=%X\n", r);
	return r;
}

#else


int callcode (FILE *fd)
{
	int r;
	union
	{
		unsigned int *ptr;
		int (*f) (FILE *);
	} u;
	u.ptr = code;
	// fprintf (out1, "appel code...\n");
	r = (*(u.f))(fd);
	// fprintf (out1, "resultat=%X\n", r);
	return r;
}

#endif

void initf (void)
{
}

#if 1

#ifdef WINDOWS
int loadasm (FILE *fd, HINSTANCE hInstance, HINSTANCE hPrevInstance, LPWSTR lpszCmdLine, int nCmdShow)
#else
int loadasm (FILE *fd)
#endif
{
	FILE *fcode;
	char line[300];
	char line1[300];
	char name[LEN];
	int trouve, chaine, i, k;
	unsigned int x;
	int r;
	char *filename;
	int endcode;

	union
	{
		unsigned int *ptr;
		int (*f) ();
	} u;

	char buffilename[120];

	endcode = 0;
	// nl = 0;
	initf ();

	/*
#ifdef DASMAS
	out1 = fopen ("\\Carte de stockage\\test\\loadasma.txt", "w");
#else
	out1 = fopen ("\\Carte de stockage\\test\\loadasm.txt", "w");
#endif
	*/

	out1 = fd;

	fprintf (out1, "Debut\n");

	/*
#ifndef DASMAS
	filename = "\\Carte de stockage\\test\\dump.txt";
#else
	filename = "\\Carte de stockage\\test\\dasma.txt";
#endif
	*/

	fprintf (out1, "Nom executable: <");
	for (i=0; exename[i]; i++)
		fprintf (out1, "%c", exename[i]);
	fprintf (out1, ">\n", exename);
	
	// strcat (exenamea, ".txt");
	fprintf (out1, "exenamea=<%s>\n",exenamea);

	sprintf (buffilename, "%s.asm.txt", exenamea);
	filename = buffilename;
	// filename = "\\Carte de stockage\\test\\dump.txt";

	fcode = fopen (filename, "r");
	if (fcode == NULL)
	{
		fprintf (out1, "Erreur ouverture <%s>\n", filename);
		return 0;
	}
	fprintf (out1, "Fichier ouvert\n");

	adr = (int) code;
	for (;;)
	{
		fgets (line, sizeof(line), fcode);
		if (feof(fcode))
			break;
		if (*line != 0 && *line != '\n' && *line != '\r' && *line != '%')
		{
			trouve = 0;
			chaine = 0;
			for (i=0; line[i]; i++)
			{
				if (line[i] == ':')
					trouve = 1;
				if (line[i] == '"')
					chaine = 1;
			}
			if (trouve)
			{
				k = 0;
				for (i=0; line[i]!=':'; i++)
				{
					if (line[i] == ',')
					{
						name[k] = 0;
						strncpy (labels[nl].name, name, LEN);
						labels[nl].value = adr;
						nl++;
						k = 0;
					}
					else
						name[k++] = line[i];
				}
				name[k] = 0;
				if (*name)
				{
					strncpy (labels[nl].name, name, LEN);
					labels[nl].value = adr;
					nl++;
				}
			}
			if (!chaine)
				// adr += 4;
			{
				int trouve = 0;
				for (i=0; line[i]!=0; i++)
				{
					if (!strncmp (line+i, "RS", 2))
					{
						int taille;
						trouve = 1;
						sscanf (line+i+2, "%X", &taille);
						adr += ((taille + 3) / 4) * 4;
						break;
					}
				}
				if (!trouve)
					adr += 4;
			}
			else /* chaine */
			{
				for (i=0; line[i]!='"'; i++);
				for (k=0; line[i+1+k]!='"' && line[i+1+k]!=0 && line[i+1+k]!='\n' && line[i+1+k]!='\r'; k++);
				fprintf (out1, "<k=%d>",k);
				adr += ((k + 4) / 4 ) * 4;
			}
		}
	}
	fclose(fcode);

	for (i=0; i<nl; i++)
		fprintf (out1, "%s=%X\n", labels[i].name, labels[i].value);

	fcode = fopen (filename, "r");
	if (fcode == NULL)
	{
		fprintf (out1, "Erreur 2eme ouverture <%s>\n",filename);
		return 0;
	}
	fprintf (out1, "Fichier ouvert\n");

	adr = (int) code;
	for (;;)
	{
		fgets (line, sizeof(line), fcode);
		if (feof(fcode))
			break;
		line[strlen(line)-1] = 0;
		if (*line!=0 && *line != '\n' && *line != '\r')
		{
			substlabels (line, line1);
			adr = asmbl (line1, adr);
		}
	}

	// for (i=0; i<=(adr-(int)code)/4; i++)
	for (i=0; i<=endcode; i++)
		fprintf (out1, "%X: %08X\n", &(code[i]), code[i]);

	fprintf (out1, "appel code...\n");
#ifdef WINDOWS
	r = callcode (fd, hInstance, hPrevInstance, lpszCmdLine, nCmdShow);
#else
r = callcode (fd);
#endif
	fprintf (out1, "resultat=%X\n", r);

	fclose(out1);
}


// int loadasm (FILE *fd, HINSTANCE hInstance, HINSTANCE hPrevInstance, LPWSTR lpszCmdLine, int nCmdShow)

int loadasm1 (int *adr1, char *filename)
{
	FILE *fd;
	FILE *fcode;
	char line[300];
	char line1[300];
	char name[LEN];
	int trouve, chaine, i, k;
	unsigned int x;
	int r;
	// char *filename;
	int endcode;

	union
	{
		unsigned int *ptr;
		int (*f) ();
	} u;

	char buffilename[120];

	fd = fopen ("outasm.txt", "w");

	endcode = 0;
	// nl = 0;
	// initf ();

	/*
#ifdef DASMAS
	out1 = fopen ("\\Carte de stockage\\test\\loadasma.txt", "w");
#else
	out1 = fopen ("\\Carte de stockage\\test\\loadasm.txt", "w");
#endif
	*/

	out1 = fd;

	fprintf (out1, "Debut\n");

	/*
#ifndef DASMAS
	filename = "\\Carte de stockage\\test\\dump.txt";
#else
	filename = "\\Carte de stockage\\test\\dasma.txt";
#endif
	*/

	fprintf (out1, "Nom executable: <");
	for (i=0; exename[i]; i++)
		fprintf (out1, "%c", exename[i]);
	fprintf (out1, ">\n", exename);
	
	// strcat (exenamea, ".txt");
	fprintf (out1, "exenamea=<%s>\n",exenamea);

	// sprintf (buffilename, "%s.asm.txt", exenamea);
	// filename = buffilename;
	// filename = "\\Carte de stockage\\test\\dump.txt";

	fcode = fopen (filename, "r");
	if (fcode == NULL)
	{
		fprintf (out1, "Erreur ouverture <%s>\n", filename);
		return 0;
	}
	fprintf (out1, "Fichier ouvert\n");

	// adr = (int) code;
	adr = (int)adr1;
	for (;;)
	{
		fgets (line, sizeof(line), fcode);
		if (feof(fcode))
			break;
		if (*line != 0 && *line != '\n' && *line != '\r' && *line != '%')
		{
			trouve = 0;
			chaine = 0;
			for (i=0; line[i]; i++)
			{
				if (line[i] == ':')
					trouve = 1;
				if (line[i] == '"')
					chaine = 1;
			}
			if (trouve)
			{
				k = 0;
				for (i=0; line[i]!=':'; i++)
				{
					if (line[i] == ',')
					{
						name[k] = 0;
						strncpy (labels[nl].name, name, LEN);
						labels[nl].value = adr;
						nl++;
						k = 0;
					}
					else
						name[k++] = line[i];
				}
				name[k] = 0;
				if (*name)
				{
					strncpy (labels[nl].name, name, LEN);
					labels[nl].value = adr;
					nl++;
				}
			}
			if (!chaine)
				// adr += 4;
			{
				int trouve = 0;
				for (i=0; line[i]!=0; i++)
				{
					if (!strncmp (line+i, "RS", 2))
					{
						int taille;
						trouve = 1;
						sscanf (line+i+2, "%X", &taille);
						adr += ((taille + 3) / 4) * 4;
						break;
					}
				}
				if (!trouve)
					adr += 4;
			}
			else /* chaine */
			{
				for (i=0; line[i]!='"'; i++);
				for (k=0; line[i+1+k]!='"' && line[i+1+k]!=0 && line[i+1+k]!='\n' && line[i+1+k]!='\r'; k++);
				fprintf (out1, "<k=%d>",k);
				adr += ((k + 4) / 4 ) * 4;
			}
		}
	}
	fclose(fcode);

	for (i=0; i<nl; i++)
		fprintf (out1, "%s=%X\n", labels[i].name, labels[i].value);

	fcode = fopen (filename, "r");
	if (fcode == NULL)
	{
		fprintf (out1, "Erreur 2eme ouverture <%s>\n",filename);
		return 0;
	}
	fprintf (out1, "Fichier ouvert\n");

	// adr = (int) code;
	adr = (int)adr1;
	for (;;)
	{
		fgets (line, sizeof(line), fcode);
		if (feof(fcode))
			break;
		line[strlen(line)-1] = 0;
		if (*line!=0 && *line != '\n' && *line != '\r')
		{
			substlabels (line, line1);
			adr = asmbl (line1, adr);
		}
	}

	// for (i=0; i<=(adr-(int)code)/4; i++)
	for (i=0; i<=endcode; i++)
		fprintf (out1, "%X: %08X\n", &(code[i]), code[i]);

	fprintf (out1, "appel code...\n");
	// r = callcode (fd, hInstance, hPrevInstance, lpszCmdLine, nCmdShow);
	fprintf (out1, "resultat=%X\n", r);

	fclose(out1);

	return adr;
}

char *getline (char *ptr, char *line)
{
 while (*ptr != '\n' && *ptr != '\r' && *ptr != 0)
  *line++ = *ptr++;
 *line++ = *ptr++;
 *line++ = 0;
 return ptr;
}

int asmem (int *adr1, char *asmcode)
{
	FILE *fd;
	FILE *fcode;
	char line[300];
	wchar_t wline[300];
	int j;
	char line1[300];
	char name[LEN];
	int trouve, chaine, i, k;
	unsigned int x;
	int r;
	// char *filename;
	int endcode;

	char *ptr;

	union
	{
		unsigned int *ptr;
		int (*f) ();
	} u;

	char buffilename[120];

	TRACE "asmem\n" ENDTRACE

	// fd = fopen ("outasm.txt", "w");
	fd = ftrace; 

	endcode = 0;
	// nl = 0;
	// initf ();

	/*
#ifdef DASMAS
	out1 = fopen ("\\Carte de stockage\\test\\loadasma.txt", "w");
#else
	out1 = fopen ("\\Carte de stockage\\test\\loadasm.txt", "w");
#endif
	*/

	out1 = fd;

	TRACE "Debut\n" ENDTRACE

	/*
#ifndef DASMAS
	filename = "\\Carte de stockage\\test\\dump.txt";
#else
	filename = "\\Carte de stockage\\test\\dasma.txt";
#endif
	*/

	fprintf (out1, "Nom executable: <");
	for (i=0; exename[i]; i++)
		fprintf (out1, "%c", exename[i]);
	fprintf (out1, ">\n", exename);
	
	// strcat (exenamea, ".txt");
	fprintf (out1, "exenamea=<%s>\n",exenamea);

	// sprintf (buffilename, "%s.asm.txt", exenamea);
	// filename = buffilename;
	// filename = "\\Carte de stockage\\test\\dump.txt";

	/*
	fcode = fopen (filename, "r");
	if (fcode == NULL)
	{
		fprintf (out1, "Erreur ouverture <%s>\n", filename);
		return 0;
	}
	fprintf (out1, "Fichier ouvert\n");
	*/
	ptr = asmcode;

	// adr = (int) code;
	adr = (int)adr1;
	TRACE "avant boucle\n" ENDTRACE
	for (;;)
	{
		TRACE "debut boucle\n" ENDTRACE
		// fgets (line, sizeof(line), fcode);
		ptr = getline (ptr, line);
		TRACE "ptr=%X line=<%s>\n", ptr, line ENDTRACE
		// if (feof(fcode))
		if (*ptr == 0)
		{
			TRACE "fin\n" ENDTRACE
			break;
		}
		TRACE "test ligne\n" ENDTRACE
		if (*line != 0 && *line != '\n' && *line != '\r' && *line != '%')
		{
			TRACE "ligne a traiter\n" ENDTRACE
			trouve = 0;
			chaine = 0;
			for (i=0; line[i]; i++)
			{
				if (line[i] == ':')
					trouve = 1;
				if (line[i] == '"')
					chaine = 1;
			}
			if (trouve)
			{
				k = 0;
				for (i=0; line[i]!=':'; i++)
				{
					if (line[i] == ',')
					{
						name[k] = 0;
						strncpy (labels[nl].name, name, LEN);
						labels[nl].value = adr;
						nl++;
						k = 0;
					}
					else
						name[k++] = line[i];
				}
				name[k] = 0;
				if (*name)
				{
					strncpy (labels[nl].name, name, LEN);
					labels[nl].value = adr;
					nl++;
				}
			}
			if (!chaine)
				// adr += 4;
			{
				int trouve = 0;
				for (i=0; line[i]!=0; i++)
				{
					if (!strncmp (line+i, "RS", 2))
					{
						int taille;
						trouve = 1;
						sscanf (line+i+2, "%X", &taille);
						adr += ((taille + 3) / 4) * 4;
						break;
					}
				}
				if (!trouve)
					adr += 4;
			}
			else /* chaine */
			{
				for (i=0; line[i]!='"'; i++);
				for (k=0; line[i+1+k]!='"' && line[i+1+k]!=0 && line[i+1+k]!='\n' && line[i+1+k]!='\r'; k++);
				fprintf (out1, "<k=%d>",k);
				adr += ((k + 4) / 4 ) * 4;
			}
			TRACE "fin traitement ligne\n" ENDTRACE
		}
		TRACE "fin boucle\n" ENDTRACE
	}
	TRACE "apres boucle\n" ENDTRACE
	// fclose(fcode);

	for (i=0; i<nl; i++)
		fprintf (out1, "%s=%X\n", labels[i].name, labels[i].value);

	/*
	fcode = fopen (filename, "r");
	if (fcode == NULL)
	{
		fprintf (out1, "Erreur 2eme ouverture <%s>\n",filename);
		return 0;
	}
	fprintf (out1, "Fichier ouvert\n");
	*/
	TRACE "2eme passe\n" ENDTRACE
	ptr = asmcode;

	// adr = (int) code;
	adr = (int)adr1;
	TRACE "avant boucle\n" ENDTRACE
	for (;;)
	{
		TRACE "debut boucle\n" ENDTRACE
		// fgets (line, sizeof(line), fcode);
		ptr = getline (ptr, line);
		TRACE "line=<%s>\n", line ENDTRACE
		// for (j=0; line[j]; j++) wline[j]=line[j]; wline[j]=0;
		// MessageBox (NULL, wline, L"line", MB_OK);
		// if (feof(fcode))
		
		TRACE "traitement\n" ENDTRACE
		line[strlen(line)-1] = 0;
		TRACE "test\n" ENDTRACE
		if (*line!=0 && *line != '\n' && *line != '\r')
		{
			TRACE "substlabels\n" ENDTRACE
			substlabels (line, line1);
			TRACE "adr=%X line1=<%s>\n", adr, line1 ENDTRACE
			adr = asmbl (line1, adr);
			TRACE "adr=%X\n",adr ENDTRACE
		}
		if (*ptr == 0)
		{
			TRACE "fin\n" ENDTRACE
			break;
		}
		TRACE "fin boucle\n" ENDTRACE
	}
	TRACE "apres boucle\n" ENDTRACE

#if 0
	// for (i=0; i<=(adr-(int)code)/4; i++)
	for (i=0; i<=endcode; i++)
		fprintf (out1, "%X: %08X\n", &(code[i]), code[i]);

	fprintf (out1, "appel code...\n");
	// r = callcode (fd, hInstance, hPrevInstance, lpszCmdLine, nCmdShow);
	fprintf (out1, "resultat=%X\n", r);

	// fclose(out1);
#endif

	TRACE "end asmem adr=%X\n", adr ENDTRACE
	return adr;
}




#endif

/*** desassembleur ***/


unsigned int field (unsigned int x, unsigned int mask)
{
	while ((mask & 1) == 0)
	{
		mask = mask >> 1;
		x = x >> 1;
	}
	return x & mask;
}

int sfield (unsigned int x, unsigned int mask)
{
	unsigned int sp, s;
	while ((mask & 1) == 0)
	{
		mask = mask >> 1;
		x = x >> 1;
	}
	sp = (mask+1)>>1;
	s = x & sp;
	if (s == 0)
		return x & mask;
	else
		// return -((~(x & mask)) + 1);
		return (x & mask) | ~mask;
}

unsigned int rotate (unsigned int x, unsigned int r)
{
	return (x>>r) | (x<<(32-r));
}


void printasm (char *s, unsigned int x, unsigned int adr)
{
	char buf[1000];
	int i, j;
	char *cond[] = { "==", "!=", "c", "!c", "<0", ">=0",  "OVF", "!OVF", "HI", "LS", ">=", "<", ">", "<=", "", "UNC" };
	char *op[] = { "&", "!", "-", "*-1+", "+", "+c+", "-!c-", "*-1-!c+", "?&", "?!", "?-", "?+", "|", "->", "&!", "->~" };
	// char *shift[] = { "LSL", "LSR", "ASR",  "RR" };
	char *shift[] = { "<<", ">>", "->>", ">>>" };
	unsigned int Rn, Rd, Rs, Rm;
	unsigned int adr1;
	int adrinstr;
	int trouve;

	adrinstr = adr;

	Rn = field (x, 0xF0000);
	Rd = field (x, 0xF000);
	Rs = field (x, 0xF00);
	Rm = field (x, 0xF);

	i = 0;

	for (j=0; j<nadr; j++)
		if (x == tabadr[j].adr)
		{
			if (dasm)
			{
				i += sprintf (buf+i, "%s", tabadr[j].name);
				goto outbuf;
			}
			else
				i += sprintf (buf+i, "#%X == %s ", x, tabadr[j].name);
		}

	/*
	if (x >= beginstrings && x <= endstrings)
	{
		i += sprintf (buf+i, "strings+%X", x-beginstrings);
		goto outbuf;
	}
	*/

	i += sprintf (buf+i, cond[x>>28]);
	// i += sprintf (buf+i, "(%x)", x>>28);
	i += sprintf (buf+i, " ");

	if (match (x, 0x1200010, 0xFF000F0))
		i += sprintf (buf+i, "BX [R%X]", Rm);

	else if (match (x, 0xF0000000, 0xF0000000)) /* unconditional */
		i += sprintf (buf+i, "#%07X", x & 0xFFFFFFF);

	/*
	else if (match (x, 0xA000000, 0xF000000))
		i += sprintf (buf+i, "B RF+4*%X == %X", field (x, 0xFFFFFF), adr+8+4*sfield(x,0xFFFFFF));
	*/
	else if (match (x, 0xA000000, 0xF000000))
	{
		// i += sprintf (buf+i, "BL RF+4*%X == %X",  field (x, 0xFFFFFF), adr+8+4*sfield(x,0xFFFFFF));
		trouve = 0;
		for (j=0; j<nadr; j++)
			if ((int)(tabadr[j].adr) == adr+8+4*sfield(x,0xFFFFFF))
			{
				trouve = 1;
				i += sprintf (buf+i, "GOTO %s", tabadr[j].name);
			}
		if (!trouve)
			i += sprintf (buf+i, "GOTO %X", adr+8+4*sfield(x,0xFFFFFF));
	}

	else if (match (x, 0xB000000, 0xF000000))
	{
		// i += sprintf (buf+i, "BL RF+4*%X == %X",  field (x, 0xFFFFFF), adr+8+4*sfield(x,0xFFFFFF));
		trouve = 0;
		for (j=0; j<nadr; j++)
			if ((int)(tabadr[j].adr) == adr+8+4*sfield(x,0xFFFFFF))
			{
				trouve = 1;
				i += sprintf (buf+i, "%s ()", tabadr[j].name);
			}
		if (!trouve)
			i += sprintf (buf+i, "%X ()", adr+8+4*sfield(x,0xFFFFFF));
	}
	else if (match (x, 0x1000000, 0xF900010)) /* misc */
		// i += sprintf (buf+i, "#%07X misc", x & 0xFFFFFFF);
		i += sprintf (buf, "%X", x);
	else if (match (x, 0x1000010, 0xF900090)) /* misc */
		// i += sprintf (buf+i, "#%07X misc", x & 0xFFFFFFF);
		i += sprintf (buf, "%X", x);

	/*
	else if (match (x, 0x3A00000, 0xFFF0F00))
		i += sprintf (buf+i, "R%X=%X", field (x, 0xF000), field (x, 0xFF));
	else if (match (x, 0x1A00000, 0xFFF0FF0))
		i += sprintf (buf+i, "R%X=R%X", field (x, 0xF000), field (x, 0xF));
	else if (match (x, 0x2800000, 0xFF00F00))
		i += sprintf (buf+i, "R%X=R%X+%X", field (x, 0xF000), field (x, 0xF0000), field (x, 0xFF));
	else if (match (x, 0x0800000, 0xFF00FF0))
		i += sprintf (buf+i, "R%X=R%X+R%X", field (x, 0xF000), field (x, 0xF0000), field (x, 0xF));
	else if (match (x, 0x2400000, 0xFF00F00))
		i += sprintf (buf+i, "R%X=R%X-%X", field (x, 0xF000), field (x, 0xF0000), field (x, 0xFF));
	else if (match (x, 0x0400000, 0xFF00FF0))
		i += sprintf (buf+i, "R%X=R%X-R%X", field (x, 0xF000), field (x, 0xF0000), field (x, 0xF));
	
	else if (match (x, 0x5900000, 0xFF00000))
		i += sprintf (buf+i, "R%X=[R%X+%X]", field (x, 0xF000), field (x, 0xF0000), field (x, 0xFFF));
	else if (match (x, 0x5800000, 0xFF00000))
		i += sprintf (buf+i, "[R%X+%X]=R%X", field (x, 0xF0000), field (x, 0xFFF), field (x, 0xF000));
	*/

	else if (match (x, 0x9200000, 0xFF00000))
		i += sprintf (buf+i, "PUSH R%X %04X", field (x, 0xF0000), field (x, 0xFFFF));
	else if (match (x, 0x8B00000, 0xFF00000))
		i += sprintf (buf+i, "POP R%X %04X", field (x, 0xF0000), field (x, 0xFFFF));

	else if (match (x, 0x1A00000, 0xFF00FF0)) /* move with register */
		i += sprintf (buf+i, "R%X = R%X", Rd, Rm);
	else if (match (x, 0x1B00000, 0xFF00010)) /* move with register, update condition codes */
		i += sprintf (buf+i, "R%X ?= R%X", Rd, Rm);

	else if (match (x, 0x1A00000, 0xFF00010)) /* move with register shifted by immediate */
		i += sprintf (buf+i, "R%X = R%X %s %X", Rd, Rm, shift[field(x,0x60)], field(x,0xF80));
	else if (match (x, 0x1B00000, 0xFF00010)) /* move with register shifted by immediate, update condition codes */
		i += sprintf (buf+i, "R%X ?= R%X %s %X", Rd, Rm, shift[field(x,0x60)], field(x,0xF80));
	else if (match (x, 0x1A00010, 0xFF00090)) /* move with register shifted by register */
		i += sprintf (buf+i, "R%X = R%X %s R%X", Rd, Rm, shift[field(x,0x60)], Rs);
	else if (match (x, 0x1B00010, 0xFF00090)) /* move with register shifted by register, update condition codes */
		i += sprintf (buf+i, "R%X ?= R%X %s R%X", Rd, Rm, shift[field(x,0x60)], Rs);
	else if (match (x, 0x3A00000, 0xFF00000)) /* move immediate */
		i += sprintf (buf+i, "R%X = %X", Rd, rotate (field(x,0xFF), field(x,0xF00)));
	else if (match (x, 0x3B00000, 0xFF00000)) /* move immediate, update condition codes */
		i += sprintf (buf+i, "R%X ?= %X", Rd, rotate (field(x,0xFF), field(x,0xF00)));

	else if (match (x, 0x0000000, 0xE100FF0)) /* data processing with register */
		i += sprintf (buf+i, "R%X = R%X %s R%X", Rd, Rn, op[field(x,0x1E00000)], Rm);
	else if (match (x, 0x0100000, 0xE100FF0)) /* data processing with register, update condition codes */
		i += sprintf (buf+i, "R%X ?= R%X %s R%X", Rd, Rn, op[field(x,0x1E00000)], Rm);

	else if (match (x, 0x0000000, 0xE100010)) /* data processing with register shifted by immediate */
		i += sprintf (buf+i, "R%X = R%X %s R%X %s %X", Rd, Rn, op[field(x,0x1E00000)], Rm, shift[field(x,0x60)], field(x,0xF80));
	else if (match (x, 0x0100000, 0xE100010)) /* data processing with register shifted by immediate, update condition codes */
		i += sprintf (buf+i, "R%X ?= R%X %s R%X %s %X", Rd, Rn, op[field(x,0x1E00000)], Rm, shift[field(x,0x60)], field(x,0xF80));
	else if (match (x, 0x0000010, 0xE100090)) /* data processing with register shifted by register */
		i += sprintf (buf+i, "R%X = R%X %s R%X %s R%X", Rd, Rn, op[field(x,0x1E00000)], Rm, shift[field(x,0x60)], Rs);
	else if (match (x, 0x0100010, 0xE100090)) /* data processing with register shifted by register, update condition codes */
		i += sprintf (buf+i, "R%X ?= R%X %s R%X %s R%X", Rd, Rn, op[field(x,0x1E00000)], Rm, shift[field(x,0x60)], Rs);
	else if (match (x, 0x2000000, 0xE100000)) /* data processing immediate */
		i += sprintf (buf+i, "R%X = R%X %s %X", Rd, Rn, op[field(x,0x1E00000)], rotate (field(x,0xFF), field(x,0xF00)));
	else if (match (x, 0x2100000, 0xE100000)) /* data processing immediate, update condition codes */
		i += sprintf (buf+i, "R%X ?= R%X %s %X", Rd, Rn, op[field(x,0x1E00000)], rotate (field(x,0xFF), field(x,0xF00)));

	else if (match (x, 0x4000000, 0xE000000)) /* load store immediate offset */
	{
		char s;
		char *af;
		char adr[30];
		char mem[30];
		unsigned int im;
		if (x & 0x800000)
			s = '+';
		else
			s = '-';
		im = field(x,0xFFF);
		if (match (x, 0x4000000, 0xF200000))
		{
			af = "=";
			sprintf (adr, "R%X,%c=%X", Rn, s, im);
		}
		else if (match (x, 0x4200000, 0xF200000))
		{
			af = "=U";
			sprintf (adr, "R%X,%c=%X", Rn, s, im);
		}
		else if (match (x, 0x5000000, 0xF200000))
		{
			af = "=";
			sprintf (adr, "R%X%c%X", Rn, s, im);
			if (Rn == 0xF)
			{ 
				if (s == '+')
					adr1 = adrinstr + 8 + im;
				else
					adr1 = adrinstr + 8 - im;
				if (dasm)
					sprintf (adr, "%X", adr1);
				else
					sprintf (adr+strlen(adr), "==%X", adr1);
				for (j=0; j<nadr; j++)
					if (adr1 == tabadr[j].adr)
					{
						if (dasm)
							sprintf (adr, "%s", tabadr[j].name);
						else
							sprintf (adr+strlen(adr), "==%s", tabadr[j].name);
					}
					
			}
		}
		else if (match (x, 0x5200000, 0xF200000))
		{
			af = "=";
			sprintf (adr, "R%X%c=%X", Rn, s, im);
		}
		if (x & 0x400000)
			sprintf (mem, "$[%s]", adr);
		else
			sprintf (mem, "[%s]", adr);
		if (x & 0x100000)
			i += sprintf (buf+i, "R%X %s %s", Rd, af, mem);
		else
			i += sprintf (buf+i, "%s %s R%X", mem, af, Rd);
		
	}

	else if (match (x, 0x6000000, 0xE000010)) /* load store register offset */
	{
		char s;
		char *af;
		char adr[30];
		char mem[30];
		char im[30];
//	fprintf (fdasm, "*1*");
		if (x & 0x800000)
			s = '+';
		else
			s = '-';
//	fprintf (fdasm, "*2*");
		sprintf (im, "R%X %s %X", Rm, shift[field(x,0x60)], field(x,0xF80));
//	fprintf (fdasm, "*3*");
		if (match (x, 0x6000000, 0xF200000))
		{
			af = "=";
			sprintf (adr, "R%X,%c=%s", Rn, s, im);
		}
		else if (match (x, 0x6200000, 0xF200000))
		{
			af = "=U";
			sprintf (adr, "R%X,%c=%s", Rn, s, im);
		}
		else if (match (x, 0x7000000, 0xF200000))
		{
			af = "=";
			sprintf (adr, "R%X%c%s", Rn, s, im);
		}
		else if (match (x, 0x7200000, 0xF200000))
		{
			af = "=";
			sprintf (adr, "R%X%c=%s", Rn, s, im);
		}
		else
		{
			af = "?";
			sprintf (adr, "?");
		}
//	fprintf (fdasm, "*4");
		if (x & 0x400000)
			sprintf (mem, "$[ %s]", adr);
		else
			sprintf (mem, "[%s]", adr);
/*	fprintf (fdasm, "*5*");
	fprintf (fdasm, "*i=%d*", i);
	fprintf (fdasm, "*Rd=%X*", Rd);
	fprintf (fdasm, "*af=%s*", af);
	fprintf (fdasm, "*mem=%s*", mem);
*/		if (!strcmp (af, "?"))
			i += sprintf (buf, "%X", x);
		else if (x & 0x100000)
			i += sprintf (buf+i, "R%X %s %s", Rd, af, mem);
		else
			i += sprintf (buf+i, "%s %s R%X", mem, af, Rd);
//	fprintf (fdasm, "*6");
	}

	else if (match (x, 0x8000000, 0xE000000)) /* load store multiple */
	{
		char mem[30];
		char *af;

		if (x & 0x400000)
			af = "?=";
		else
			af = "=";

		if (match (x, 0x8000000, 0xFA00000)) sprintf (mem, "[R%X-]", Rn); else 
		if (match (x, 0x8200000, 0xFA00000)) sprintf (mem, "[R%X-=]", Rn); else
		if (match (x, 0x8800000, 0xFA00000)) sprintf (mem, "[R%X+]", Rn); else
		if (match (x, 0x8A00000, 0xFA00000)) sprintf (mem, "[R%X+=]", Rn); else
		if (match (x, 0x9000000, 0xFA00000)) sprintf (mem, "[R%X--]", Rn); else
		if (match (x, 0x9200000, 0xFA00000)) sprintf (mem, "[R%X--=]", Rn); else
		if (match (x, 0x9800000, 0xFA00000)) sprintf (mem, "[R%X++]", Rn); else
		if (match (x, 0x9A00000, 0xFA00000)) sprintf (mem, "[R%X++=]", Rn); else
		sprintf (mem, "?");

		if (x & 0x100000)
			i += sprintf (buf+i, "RR#%04X %s %s", field(x,0xFFFF), af, mem);
		else
			i += sprintf (buf+i, "%s %s RR#%04X", mem, af, field(x,0xFFFF));
			
	}

	else if (match (x, 0x1000090, 0xFF00FF0)) /* swap */
		i += sprintf (buf+i, "R%X = [R%X] = R%X", Rd, Rn, Rm);
	else if (match (x, 0x1400090, 0xFF00FF0)) /* swap bytes */
		i += sprintf (buf+i, "R%X = $[R%X] = R%X", Rd, Rn, Rm);

	else if (match (x, 0x1900F9F, 0xFF00FFF)) /* LDREX */
		i += sprintf (buf+i, "R%X X= [R%X]", Rd, Rn);
	else if (match (x, 0x1800F9F, 0xFF00FFF)) /* STREX */
		i += sprintf (buf+i, "[R%X] X= R%X", Rn, Rd);

	else if (match (x, 0x19000D0, 0xFF00FF0)) /* load signed byte register offset */
		i += sprintf (buf+i, "R%X = +$[R%X+R%X]", Rd, Rn, Rm);

	else if (match (x, 0x04000D0, 0xE4000F0))
	{
		char mem[30];
		char s;
		unsigned int ofs;
		ofs = (x&0xF) | ((x&0xF00)>>4);
		if (x & 0x800000)
			s = '+';
		else
			s = '-';
		if (match (x, 0x04000D0, 0xE6000F0))
			sprintf (mem, "$$[R%X,%c=%X]", Rn, s, ofs);
		else if (match (x, 0x14000D0, 0xE6000F0))
			sprintf (mem, "$$[R%X%c=%X]", Rn, s, ofs);
		else if (match (x, 0x16000D0, 0xE6000F0))
			sprintf (mem, "$$[R%X%c%X]", Rn, s, ofs);
		else
			sprintf (mem, "[?]");
		if (x & 100000)
			i += sprintf (buf+i, "R%X = %s", Rd, mem);
		else
			i += sprintf (buf+i, "%s = R%X", mem, Rd);
	}

	else if (match (x, 0x0000090, 0xFF0F0F0))
		i += sprintf (buf+i, "R%X = R%X * R%X", field(x,0xF0000), field(x,0xF00), field(x,0xF));

	else
		i += sprintf (buf, "%X", x);
outbuf:
	buf[i] = 0;
	// fprintf (out1, "%s", buf);
	sprintf (s, "%s", buf);
}


void printascii (FILE *out, unsigned int x)
{
	int i;
	fprintf (out, "   \"");
	for (i=0; i<4; i++)
	{
		char c;
		c = x>>8*i;
		if (c >= 0x20 && c <= 0x7E)
			fprintf (out, "%c", c);
		else
			fprintf (out, ".");
	}
	fprintf (out, "\"");
}


void dumpcode (FILE *fdasm, char *s, void *a, void *b)
{
	unsigned int *p;
	char buf[300];
	// labels[l] = a;

	if (dasm)
	{
		if (*s)
			fprintf (fdasm, "%s,", s);
	}
	// else
	//	fprintf (fdasm, "@%X %s\n", l, s);

	
	for (p=(unsigned int *)a; p<(unsigned int *)b; p++)
	{
		if (dasm)
			fprintf (fdasm, "%X: ", p);
		else
			fprintf (fdasm, "%08X %8X ", *p, p);
		// printasm (fdasm, *p, (unsigned int)p);
		printasm (buf, *p, (unsigned int)p);
		fprintf (fdasm, "%s", buf);
		// fprintf (out1, "   \"%c%c%c%c\"\n", *p, *p>>8, *p>>16, *p>>24);
		if (!dasm)
			printascii (fdasm, *p);
		if (dasm)
			fprintf (fdasm, " \t %% %X", *p);
		fprintf (fdasm, "\n");
	}
	

	fprintf (fdasm, "\n");
}

void dumpstring (FILE *fdasm, char *s, void *a, void *b)
{
	char *p;
	// labels[l] = a;

	if (dasm)
		fprintf (fdasm, "%s,", s);
	// else
	//	fprintf (fdasm, "@%X %s\n", l, s);
	
	if (dasm)
		fprintf (fdasm, "%X: ", a);
	else
		fprintf (fdasm, "%08X %8X ", *p, p);

	fprintf (fdasm, "\"");

	for (p=(char *)a; p<(char *)b; p++)
		if (*p >= 0x20 && *p <= 0x7E)
			fprintf (fdasm, "%c", *p);

	fprintf (fdasm, "\"\n\n");
}

void dumpdata (FILE *fdasm, char *s, void *a, void *b)
{
	unsigned int *p;
	fprintf (fdasm, "%s,%X: ", s, a);
	for (p=(unsigned int *)a; p<(unsigned int *)b; p++)
		fprintf (fdasm, "%08X\n", *p);
	fprintf (fdasm, "\n");
}

void dumpdatasize (FILE *fdasm, char *s,void *a, int size)
{
	int i;
	fprintf (fdasm, "%s,%X: ", s, a);
	for (i=0; i<(size+3)/4; i++)
		fprintf (fdasm, "%08X\n", ((unsigned int *)a)[i]);
	fprintf (fdasm, "\n");
}

void dumpvar (FILE *fdasm, char *s, int size)
{
	int sizea;
	sizea = ((size+3) / 4) * 4;
	fprintf (fdasm, "%s: RS %X\n", s, sizea);
}


