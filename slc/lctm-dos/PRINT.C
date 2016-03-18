
#include "lctm.h"

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

print_dem (struct print_param *p, DEM d)
{
int i, dp;
    switch (node(d))
    {
	case _Var :
	    print_string (p, name(d));
            print_string (p,":");
            print_dem (p, subdem(0,d));
	    break;

        case _I: print_strint (p, "I%d", order(d)); break;
        case _K: print_strint (p, "K%d", order(d)); break;
        case _S: print_strint (p, "S%d", order(d)); break;
        case _Y: print_strint (p, "Y%d", order(d)); break;
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
             print_string (p, "(");
             dp = depth (d);
             print_dem (p, rfnc(dp,d));
             for (i=dp-1; i>=0; i--)
             {
                 print_string (p, " ");
                 print_dem (p, subdem(1,rfnc(i,d))); 
             }    
             print_string (p, ")");
             break;

	case _transym:
	    print_string (p, "(transym ");
	    goto psd01;

        case _defI:
	    print_string (p, "(defI ");
	    goto psd01;

        case _defK:
	    print_string (p, "(defK ");
            print_dem (p, subdem(0,d));
	    for (i=1; i<=3; i++)
	    {
		print_string (p, " ");
		print_dem (p, subdem(i,d));
            }
            print_string (p, ")");
	    break;
    
        case _defS:
	    print_string (p, "(defS ");
            print_dem (p, subdem(0,d));
	    for (i=1; i<=5; i++)
	    {
		print_string (p, " ");
		print_dem (p, subdem(i,d));
            }
            print_string (p, ")");
	    break;    

        default: print_strint (p, "?%d", (int)(node(d))); 
        
        
             
             
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
    /* printf ("psf<%s>\n", s); */
    fprintf (p->f, "%s", s);
}

print_string_nul (struct print_param *p, char *s)
{
    if (kbhit())
        exit(0);
}

trace_dem (char *s, DEM x)
{
    print_string (print_param, s);
    print_dem (print_param, x); 
    print_string (print_param, "\n");		
}
