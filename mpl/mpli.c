
#include <stdlib.h>
#include <stdio.h>

typedef char *mplword;

/* #define WORDSIZE (sizeof(mplword)) */
#define WORDSIZE 8

FILE *script;
FILE *input;
FILE *output;

#define MEMSIZE 0x3000
union
{
 char c[WORDSIZE*MEMSIZE];
 mplword w[MEMSIZE];
} mem;

int adr;
char c;
int goon;
int trace;
char instr;
long pc, r0, r1, rc, ru;
long t;
int state;
#define RUN 0
#define CODE 1
char buf[1000];

openfile (char *mode)
{
 char filename[1000];
 int i;
 /* printf ("openfile r1=%X mem[r1]=%X\n", r1, mem.c[r1]); */
 i = 0;
 while (mem.c[r1+i])
 {
  filename[i] = mem.c[r1+i];
  i++;
 }
 filename[i] = 0;
 /* printf ("open file (%s) with mode (%s)\n", filename, mode); */
 r1 = (long) fopen (filename, mode);
}

main (int argc, char **argv)
{
	/* printf ("WORDSIZE=%X memory size=%X sizeof(char)=%X\n", WORDSIZE, sizeof(mem), sizeof(char)); */
	script = fopen (argv[1], "r");
	if (script == NULL)
	{
		perror (argv[1]);
		exit(0);
	}
	if ((argc < 3) || !strcmp (argv[2], "-"))
		input = stdin;
	else
	{
		input = fopen (argv[2], "r");
		if (input == NULL)
		{
			perror (argv[2]);
			exit(0);
		}
	}
	if ((argc < 4) || !strcmp (argv[3], "-"))
		output = stdout;
	else
	{
		output = fopen (argv[3], "w");
		if (output == NULL)
		{
			perror (argv[3]);
			exit(0);
		}
	}

	adr = 0;
	while (!feof(script))
	{
		c = fgetc (script);
		mem.c[adr++] = c;
	}

	trace = 0;
	goon = 1;
	pc = 0;
	r0 = 0;
	r1 = 0;
	rc = adr;

	/* printf ("Running...\n"); */
	while (goon)
	{
		/* printf (" pc=%X ", pc); */
		instr = mem.c[pc++];
		/* printf (" ok1 "); */
		if (trace & 1)
		{ 
		 /* printf (" ok3 "); */
		 /* printf (" instr=%X ", instr); */
		 putchar(instr);
		 /* printf (" ok4 "); */
		}
		/* printf (" ok2 "); */
		if (trace & 2)
		{
			printf ("\nR0=%4lX\tR1=%4lX\tRC=%4lX\tPC=%4lX\tinstr=%c ",
				r0, r1, rc, pc, instr);
			gets(buf);
		}
		fflush (stdout);
		if (state == CODE)
		{
			if (instr == '}')
				state = RUN;
			else
				mem.c[rc++] = instr;
		}
		else switch (instr)
		{
			case ',': r1 = r0; break;
			case 'X': t = r0; r0 = r1; r1 = t; break;
			case 'p': r0 = pc; break;
			case 'Q': goon = 0; break;
			case '?': if (r1 == 0) { r1 = pc; pc = r0; } break;
			/*
			case 'R': r0 = (long)(mem.w[r0/WORDSIZE]); break;
			case 'W': mem.w[r0/WORDSIZE] = (mplword)r1; break;
			*/
			case 'R': r0 = *(long *)(mem.c+r0); break;
			case 'W': if ((r0 < 0) || (r0 >= sizeof(mem))) { printf ("W : Write out of memory\n"); exit(0); } 
				  *(long *)(mem.c+r0) = r1; break;
			case 'r': r0 = mem.c[r0]; break;
			case 'w': if ((r0 < 0) || (r0 >= sizeof(mem))) { printf ("w : Write out of memory\n"); exit(0); }
				  mem.c[r0] = r1; break;
			case '#': r0 = 0; break;

			case '0': r0 = r0*16; break;
			case '1': r0 = r0*16+1; break;
			case '2': r0 = r0*16+2; break;
			case '3': r0 = r0*16+3; break;
			case '4': r0 = r0*16+4; break;
			case '5': r0 = r0*16+5; break;
			case '6': r0 = r0*16+6; break;
			case '7': r0 = r0*16+7; break;
			case '8': r0 = r0*16+8; break;
			case '9': r0 = r0*16+9; break;
			case 'A': r0 = r0*16+10; break;
			case 'B': r0 = r0*16+11; break;
			case 'C': r0 = r0*16+12; break;
			case 'D': r0 = r0*16+13; break;
			case 'E': r0 = r0*16+14; break;
			case 'F': r0 = r0*16+15; break;

			case '~': r0 = ~r0; break;
			case '+': r0 = r0 + r1; break;
			case '-': r0 = r0 - r1; break;
			case '*': r0 = r0 * r1; break;
			case '/': r0 = r0 / r1; break;
			case '%': r0 = r0 % r1; break;
			case '&': r0 = r0 & r1; break;
			case '^': r0 = r0 ^ r1; break;
			case '|': r0 = r0 | r1; break;
			case '<': r0 = r0 << r1; break;
			case '>': r0 = r0 >> r1; break;

			case 'G': if (feof(input)) r0 = -1; else r0 = fgetc(input); break;
			case 'P': fputc (r0, output); break;
			case 'H': rc = r0; break;
			case 'h': r0 = rc; break;
			case '{': state = CODE; break;
			case '}': if ((rc < 0) || (rc >= sizeof(mem))) { printf ("} : Write out of memory\n"); exit(0); }
				  mem.c[rc++] = instr; break;
			case '_': if ((rc < 0) || (rc >= sizeof(mem))) { printf ("_ : Write out of memory\n"); exit(0); }
				  mem.c[rc++] = r0; break;
			case 's': r0 = WORDSIZE; break;

			case 'S':
			 switch (r0)
			 {
			  case 0x11: openfile ("rb"); break;
			  case 0x12: openfile ("wb"); break;
			  case 0x13: openfile ("ab"); break;
			  case 0x14: openfile ("r+b"); break;
			  case 0x15: openfile ("w+b"); break;
			/*
			  case 0x1F: fclose ((FILE *)(mem.w[r1/WORDSIZE])); break;
			  case 0x20: mem.w[(r1+WORDSIZE)/WORDSIZE] = (mplword) fgetc ((FILE *)(mem.w[r1/WORDSIZE])); break;
			  case 0x21: fputc ((char)(mem.w[(r1+WORDSIZE)/WORDSIZE]), (FILE *)(mem.w[r1/WORDSIZE])); break;
			  case 0x1F: fclose (*(FILE **)(mem.c+r1)); break;
			*/
			  case 0x1F: fclose ((FILE *) r1); break;
			  case 0x20: *(long *)(mem.c+r1+WORDSIZE) = fgetc (*(FILE **)(mem.c+r1)); break;
			  case 0x21 : fputc (*(long *)(mem.c+r1+WORDSIZE), *(FILE **)(mem.c+r1)); break;
			 }

			 break;

			case 'T': trace = 2; break;
			case 't': trace = 1; break;
			case 'e': printf ("\nError\n"); goon = 0; break;

			case 'u': r0 = ru; break;
			case 'U': ru = r0; break;
			case 'J': t = r0;
				  r0 = *(long *)(mem.c+t);
				  r1 = *(long *)(mem.c+t+WORDSIZE);
				  pc = *(long *)(mem.c+t+2*WORDSIZE);
				  break;
			case ' ':
			case '\n':
			case '\r':
			case '\t':
			case ';': break;

			default: 
			 *(long *)(mem.c+ru) = r0;
			 *(long *)(mem.c+ru+WORDSIZE) = r1;
			 *(long *)(mem.c+ru+2*WORDSIZE) = pc;
			 pc = ru+3*WORDSIZE;
			 break;
		}
	}
}
