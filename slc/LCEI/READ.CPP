
#include "lctm.h"

#include <stdio.h>

FILE *file_in =
#ifdef VAXC

NULL;

int getc1 (FILE *f)
{
    if (f == NULL)
        return getc (stdin);
    else
        return getc (f);
}

int feof1 (FILE *f)
{
    if (f == NULL)
        return feof (stdin);
    else
        return feof (f);

}

#define getc getc1
#define feof feof1

#else

stdin;

#endif

int readchar1 ()
{
int c;
char filename[200];
        c = getc (file_in);
        if (feof(file_in) || c == EOF)
        {
            file_in = stdin;
            c = getc (file_in);
	}
        if (c == ';')
        {
        	gets (filename);
                file_in = fopen (filename, "r");
                if (file_in == NULL)
                {
                	perror (filename);
                        file_in = stdin;
        	}
                c = getc (file_in);
        }
        putchar (c);
        return c;
}

int com_level = 0;

int readchar ()
{
int c;
    for (;;)
    {
        c = readchar1 ();
        if (c == '{')
            com_level++;
        if (c == '}')
        {
            com_level--;
            c = readchar1 ();
        }
        if (com_level <= 0)
            return c;
    }    
}

DEM defined_dems[0x100];

DEM no_red [30];
int nnr;

DEM read_dem ()
{
int c;
DEM f, a, b, d, x;
int i;
char buf[200];
DEM s;
DEM d1;
int flags1;
DEM used1;
extern DEM used;
loop:
	do c = readchar ();
	while (c==' ' || c=='\t' || c=='\n' || c==0);

	switch (c)
	{
		case 'I': return I;
		case 'K': return K;
		case 'S': return S;
		case 'E': return E;
		case 'F': return If;
		case 'O': return Ord;

		case '-':
			f = read_dem ();
			a = read_dem ();
			return ap (f, a);

		case '/':
			a = read_dem ();
			b = read_dem ();
			return transym (a, b);

                case 'T':
                        a = read_dem ();
                        b = read_dem ();
                        return trans (a, b);

                case 'X':
                        a = read_dem ();
                        return sym (a);

                case '#':
                        a = read_dem ();
                        b = read_dem ();
                        return Axm (a, b);

		case 'i':
			a = read_dem ();
			return defI (a);

		case 'k':
			a = read_dem ();
			b = read_dem ();
			return defK (a, b);

		case 's':
			a = read_dem ();
			b = read_dem ();
                        d = read_dem ();
                        return defS (a, b, d);           

                case ')':
                        a = read_dem ();
                        b = read_dem ();
                        return IfNode (a, b);

                case '1': return Ext1;
                case '2': return Ext2;
                case '3': return Ext3;
                case '4': return Ext4;
                case '5': return Ext5;
                case '6': return Ext6;

		case 'e': return AE;
                case 'f': return EA0;
                        /*
                        a = read_dem ();        
                        return EA (a);
                        */
                case 'm': return MP;
                case 'a': return AI;
                case 'b': return AK;
                case 'c': return AS;
                case 'r': return RPA;

                case '0': return ZeroIsOrd;
                case '+': return SucIsOrd;
                case 'w': return LimIsOrd;
                case 'p': return PredIsOrd;
                case 'n': return StepIsOrd;
                case 'W': return TfI;                

                case '<':
                        a = read_dem ();
                        return left (a);

                case '>':
                        a = read_dem ();
                        return right (a);

                case '\'':
                        a = read_dem ();
                        return rep(a);

		case '%':
/*printf ("*1*");*/
			a = read_dem ();
/*printf ("*2*");*/
                        trace_dem ("read", a);
/*printf ("*3*");*/
                        b = red (a);
/*printf ("*4*");*/
                        trace_dem ("red", b);
                        return b;
			/* return red (a); */
            
                case 'R':
                        a = read_dem ();
                        return red1 (a, 0);

                case '@':
                        a = read_dem ();
                        return reduc (a, 1);
         
		case '~':
			a = read_dem ();
			return reduc (a, 0);

		case '$':
			a = read_dem ();
			return redu (a);

                case 'x':
			a = read_dem ();
			b = read_dem ();
			return ext (a, b);

                case '\\':
			a = read_dem ();
			b = read_dem ();
                        trace_dem ("^(0)", a);
                        trace_dem ("^(1)", b);
                        d = exten (a, b);
                        trace_dem ("^(r)", d);
                        return d;

                case ']':
                	a = read_dem ();
                        b = read_dem ();
                        d = dbextens (a, b);
                        return d;

                case 'l':
                        a = read_dem ();
                        b = read_dem ();
                        return Ext (a, b);
                        /* return Lambda (a, b); */

                case 'L':
                        a = read_dem ();
                        b = read_dem ();
                        return Lambda (a, b);

                case '.':
                        a = read_dem ();
                        return DBLambda (a);

                case '!':
                        a = read_dem ();
                        b = read_dem ();
                        return DB_lambda (a, b);
                        /* return DBLambda (DBname (0, a, b)); */

                case '?':
                        a = read_dem ();
                        b = read_dem ();
                        return DB_Subst (a, b);

                case '_':
                        a = read_dem ();
                        b = read_dem ();
                        d = read_dem ();
                        return Subst (a, b, d);

                case ':':
                        a = read_dem ();
                        b = read_dem ();
                        d = read_dem ();
                        return ap (exten(a,d) ,b);

                case 'V':
                        x = read_dem ();
                        d = read_dem ();
                        a = mk_dem (node(d), 0, NULL,
                                DB_lambda (x, subdem(0,d)),
                                DB_lambda (x, subdem(1,d)),
                                subdem(2,d) == NULL ? NULL :
                                DB_lambda (x, subdem(2,d)),
                                NULL, NULL, NULL);
                        return a;

                case 'A':
                        x = read_dem ();
                        d = read_dem ();
                        a = mk_dem (node(d), 0, NULL,
                                ap (x, subdem(0,d)),
                                ap (x, subdem(1,d)),
                                subdem(2,d) == NULL ? NULL :
                                ap (x, subdem(2,d)),
                                NULL, NULL, NULL);
                        return a;


                case '"':
                        a = read_dem ();
                        /* return NoRed (a); */
                        no_red[nnr++] = a;
                        return a;

                case '|':
                     a = read_dem ();
                     no_red[nnr++] = a;
                     b = read_dem ();
                     return b;

                case 'u':
                	used1 = used;
                    used = read_dem ();
                    a = read_dem ();
                    used = used1;
                    return a;
                    
                case '(':
                        flags1 = flags;
                        i = 0;
                        for (;;)
                        {
                            c = readchar ();
                            if (c == ')')
                                break;
                            buf[i++] = c;
                        }
                        buf[i] = 0;
                        sscanf (buf, "%x", &flags);
                        a = read_dem ();
                        if ((flags & FLAG_PERM) == 0)
                            flags = flags1;
                        return a;

                case ',':
                        a = read_dem ();
                        return step (a);

                case '*':
                        a = read_dem ();
                        return rstep (a);
                
                case '`':
                        a = read_dem ();
                        return list_ap (a, nil);

                case '&':
                        c = readchar ();
                        switch (c)
                        {
                                case '/': return itransym;
                                case 'i': return idefI;
                                case 'k': return idefK;
                                case 's': return idefS;
                                case '<': return ileft;
                                case '>': return iright;
                                case '=': return ieq;
                                case '#': return inode;
                                case '0': return isubdem0;
                                case '1': return isubdem1;
                                case '2': return isubdem2;
                                case '%': return ired;
                                case '$': return iredu;
                                case '\\': return iext;
                                case ',': return istep;
                                case '*': return irstep;
                                default:
                                        fprintf (stderr, "Undefined &%c.\n",
                                                 c);
                                        return I;
                        }
                        break;

                    case '[':
                        /* trace_dem ("read symbol", I); */
                        for (i=0; i<sizeof(buf); i++)
                        {
                            c = readchar();
                            if (c == ']')
                            {
                                buf[i] = 0;
#ifdef TRACE1
                                printf ("buf=<%s>\n", buf);
#endif
                                if (buf[0] >= '0' && buf[0] <= '9')
                                {
#ifdef TRACE
                                    printf ("\nDBVar <%s>", buf);
#endif
                                    d1 = DBVar (atoi(buf));
                                    trace_dem ("", d);
                                    return d1;
                                }
                                s = Sym(buf);
#ifdef TRACE1
                                trace_dem ("read symbol", s);
#endif
                                if (subdem(0,s) == NULL)
                                {
#ifdef TRACE1
                                    trace_dem ("return symbol", s);
#endif
                                    return s;
                                }
                                else
                                {
#ifdef TRACE
                                    trace_dem ("return value of", s);
#endif
                                    return subdem(0,s);
                                }

                            }
                            buf[i] = c;
                        }
                        fprintf (stderr, "Symbol too long\n");
                        return Sym(buf);

		default:
                        return defined_dems[(unsigned char)c];
                        /*
                        printf ("Illegal character 0x%02X\n", c);
			goto loop;
                        */
	}

}
