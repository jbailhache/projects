
#include "lctm.h"

int flag_parenthesis = 0;

print_string (struct print_param *p, char *s)
{
    /* printf ("ps<%s>.\n", s); */
    (*(p->print_string_param)) (p, s);
}

print_strint (struct print_param *p, char *s, int i)
{
char buf[60];
    sprintf (buf, s, i);
    print_string (p, buf);
}

print_dem1 (struct print_param *p, DEM d)
{
int i, dp;
    /* if (p->print_string_param == print_string_nul)
	return; */
    /* break_debug (); */
    if (d == NULL)
        print_string (print_param, "NULL");
    if (d == (DEM)1)
	print_string (print_param, "ONE");
    else
    switch (node(d))
    {
	case _Var :
	    print_string (p, name(d));
            print_string (p,":");
            print_dem (p, subdem(0,d));
	    break;

        case _I: print_string (p, "I"); break;
        case _K: print_string (p, "K"); break;
        case _S: print_string (p, "S"); break;
        case _E: print_string (p, "E"); break;
        case _If: print_string (p, "If"); break;
        /* case _Ord: print_string (p, "O"); break; */
 
        case _AE: print_string (p, "AE"); break;
        case _EA: print_string (p, "EA"); break;
        case _EXT: print_string (p, "EXT"); break;
        case _MP: print_string (p, "MP"); break;
        case _AI: print_string (p, "AI"); break;
        case _AK: print_string (p, "AK"); break;
        case _AS: print_string (p, "AS"); break;
        case _RPA: print_string (p, "RPA"); break;


        case _IT: print_strint (p, "IT%d", order(d)); break;
        case _KT: print_strint (p, "KT%d", order(d)); break;
        case _ST: print_strint (p, "ST%d", order(d)); break;
        case _YT: print_strint (p, "YT%d", order(d)); break;
        case _F: print_strint (p, "F%d", order(d)); break;
        case _PI: print_strint (p, "PI%d", order(d)); break;
        case _U: print_strint (p, "U%d", order(d)); break;

	case _It:
	    print_strint (p, "It%d [", order(d));
	    print_dem (p, subdem(0,d));
	    print_string (p, "]");
            break;

	case _Kt:
	    print_strint (p, "Kt%d [", order(d));
            print_dem (p, subdem(0,d));
	    print_string (p, ", ");
	    print_dem (p, subdem(1,d));
	    print_string (p, "]");
            break;

	case _St:
	    print_strint (p, "St%d [", order(d));
	    print_dem (p, subdem(0,d));
            print_string (p, ", ");
            print_dem (p, subdem(1,d));
	    print_string (p, ", ");
	    print_dem (p, subdem(2,d));
            print_string (p, "]");
            break;

	case _Yt:
	    print_strint (p, "Yt%d [", order(d));
	    print_dem (p, subdem(0,d));
	    print_string (p, "]");
            break;

	case _Ord:
	    print_string (p, "Ord");
	    break;

	case _Zero:
	    print_string (p, "Zero");
	    break;

	case _Suc:
	    print_string (p, "Suc");
	    break;

	case _Lim:
	    print_string (p, "Lim");
	    break;

	case _Rept:
	    print_string (p, "Rept [");
	    print_dem (p, subdem(0,d));
	    print_string (p, "]");
            break;

	case _Testt:
	    print_string (p, "Testt [");
	    print_dem (p, subdem(0,d));
	    print_string (p, "]");
            break;


        /*case _ap: print_string (p, "(");*/
        psd01:    print_dem (p, subdem(0,d));
                  print_string (p, " ");
                  print_dem (p, subdem(1,d));
                  print_string (p, ")");
                  break;

        case _ap:
          if (flag_parenthesis)
          {
             print_string (p, "(");
             dp = depth (d);
             print_dem (p, rfnc(dp,d));
             for (i=dp-1; i>=0; i--)
             {
                 print_string (p, " ");
                 print_dem (p, subdem(1,rfnc(i,d))); 
             }    
             print_string (p, ")");
           }
           else
           {
             print_string (p, "-");
             print_dem (p, subdem (0, d));
             print_dem (p, subdem (1, d));             
           }
           break;
	case _transym:         
	    print_string (p, "(transym ");
	    goto psd01;

        case _defI:
	    print_string (p, "(defI ");
#ifdef TYPED
	    goto psd01;
#else
            print_dem (p, subdem(0,d));
            print_string (p, " ");
	    print_string (p, ")");
            break;
#endif

        case _defK:
	    print_string (p, "(defK ");
            print_dem (p, subdem(0,d));
	    for (i=1; i<=
#ifdef TYPED
			3
#else
			1
#endif
			; i++)
	    {
		print_string (p, " ");
		print_dem (p, subdem(i,d));
            }
            print_string (p, ")");
	    break;
    
        case _defS:
	    print_string (p, "(defS ");
            print_dem (p, subdem(0,d));
	    for (i=1; i<=
#ifdef TYPED
			5
#else
			2
#endif
			; i++)
	    {
		print_string (p, " ");
		print_dem (p, subdem(i,d));
            }
            print_string (p, ")");
	    break;    

        case _Lambda:
            print_string (p, "Lambda ");
            print_dem (p, subdem(0,d));
            print_string (p, " . ");
            print_dem (p, subdem(1,d));
            break;

        /* default: print_strint (p, "?%d", (int)(node(d))); */
	default:
	    print_strint (p, "(#%d ", node(d));
            print_dem (p, subdem(0,d));
            print_string (p, ")");                          
    }

}

print_dem (struct print_param *p, DEM d)
{
int i, j, dp;
char buf[200];
#ifdef TRACE1
    printf ("%04X", d);
#endif
    /* if (p->print_string_param == print_string_nul)
	return; */
    /* break_debug (); */
    if (d == NULL)
        print_string (p, "NULL");
    else if (d == (DEM)1)
        print_string (p, "ONE");
    else if (name(d) != NULL && *name(d) )
    {
        print_string (p, "[");
        print_string (p, name(d));
        print_string (p, "]");
    }
    else
    switch (node(d))
    {
#define DP(n,s) case n: print_string (p, s); break;
	DP (_I, "I");
	DP (_K, "K");
	DP (_S, "S");
	DP (_E, "E");
	DP (_If, "F");
	DP (_Ord, "O");
	DP (_Ext1, "1");
	DP (_Ext2, "2");
	DP (_Ext3, "3");
	DP (_Ext4, "4");
	DP (_Ext5, "5");
	DP (_Ext6, "6");
	DP (_AE, "e");
        DP (_EA0, "f");
	DP (_MP, "m");
	DP (_AI, "a");
	DP (_AK, "b");
	DP (_AS, "c");
	DP (_RPA, "r");
	DP (_ZeroIsOrd, "0");
	DP (_SucIsOrd, "+");
	DP (_LimIsOrd, "w");
	DP (_PredIsOrd, "p");
	DP (_StepIsOrd, "n");
        DP (_TfI, "W");

        DP (_itransym, "&/");
        DP (_idefI, "&i");
        DP (_idefK, "&k");
        DP (_idefS, "&defS");
        DP (_ileft, "&<");
        DP (_iright, "&>");
        DP (_ieq, "&=");
        DP (_inode, "&#");
        DP (_isubdem0, "&0");
        DP (_isubdem1, "&1");
        DP (_isubdem2, "&2");
        DP (_ired, "&%");
        DP (_iredu, "&$");
        DP (_iext, "&\\");
        DP (_istep, "&,");
        DP (_irstep, "&*");

        DP (_nil, "N");

	case _ap:
		print_string (p, "-");               
	p01:
		print_dem (p, subdem (0, d));
		print_dem (p, subdem (1, d));
		break;

	case _transym:
		print_string (p, "/");
		goto p01;

        case _Axm:
                print_string (p, "#");
                goto p01;

        case _defI:
		print_string (p, "i");
		print_dem (p, subdem (0, d));
		break;

	case _defK:
                print_string (p, "k");
		goto p01;

        case _defS:
                print_string (p, "s");
		print_dem (p, subdem (0, d));
		print_dem (p, subdem (1, d));
		print_dem (p, subdem (2, d));
		break;

        case _Ext:
                print_string (p, "l");
                print_dem (p, subdem(0,d));
                print_dem (p, subdem(1,d));
                break;
                
        case _Lambda:
                print_string (p, "\\" /*"L"*/);
                print_dem (p, subdem(0,d));
                print_dem (p, subdem(1,d));
                break;

        case _DBLambda:
                print_string (p, ".");
                print_dem (p, subdem(0,d));
                break;

        case _DBVar:
                print_string (p, "[");
                print_strint (p, "%d", level(d));
                print_string (p, "]");
                break;

        case _DB_Subst:
                print_string (p, "?");
                print_dem (p, subdem(0,d));
                print_dem (p, subdem(1,d));
                break;

        case _Subst:
                print_string (p, "_");
                print_dem (p, subdem(0,d));
                print_dem (p, subdem(1,d));
                print_dem (p, subdem(2,d));
                break;

        case _NoRed:
                print_string (p, "\"");
                print_dem (p, subdem(0,d));
                break;

        case _cons:
             print_string (p, ".");
             print_dem (p, subdem(0,d));
             print_dem (p, subdem(1,d));
             break;

        case _Sym:
#ifdef TRACE1
            printf ("buf=<%s>, name=<%s>\n", d->_buf, d->_name);
#endif
            print_string (p, "[");
#ifdef ALLOC
            for (j=0; 1; j++)
            {
                buf[j] = name(d)[j];
                if (buf[j] == 0)
                    break;
            }
            print_string (p, buf);
#else
            print_string (p, name(d)); 
#endif
            print_string (p, "]");
            break;

         default:
             print_strint (p, "?(%d)", node(d));
    }
}

/*
struct print_param_file
{
    int (*print_string_param) (struct print_param *p, char *s);
    FILE *f;
};
*/

/* struct print_param_file print_param[1]; */

print_string_file (struct print_param_file *p, char *s)
{
    /* printf ("psf<%s> %x %x\n", s, p->f, stdout);  */
    fprintf (p->f, "%s", s);
}

int trace;

print_string_nul (struct print_param *p, char *s)
{
    if (trace)
       printf ("%s", s);
/*    else if (kbhit())
        exit(0);
*/
}

/*
trace_dem (char *s, DEM x)
{
    print_string (print_param, s);
    print_dem (print_param, x); 
    print_string (print_param, "\n");		
}
*/
