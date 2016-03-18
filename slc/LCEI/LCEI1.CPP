
#include "lctm.h"

struct
#ifdef CPP
        print_param
#else
        print_param_file
#endif
                print_param_err[1];

extern int flag_trace;

void break_debug (void)
{
}

error (char *s, char *file, int line, DEM d)
{
    fprintf (stderr, "Error in %s at line %d : %s ", file, line, s);
    print_dem (print_param_err, d);
#ifdef CPP
#else
    exit (1);
#endif    
}

init_print_global ()
{
/* FILE *nul;
    nul = fopen ("NUL:", "w"); */
union
{
    struct print_param_file *ppf;
    struct print_param *pp;
} u;

    print_param->print_string_param = print_string_nul;

#ifdef CPP
    (void *)
#endif
    (print_param_err->print_string_param) =
#ifdef CPP
    (void *)
#endif
    print_string_file;
#ifndef CPP
    print_param_err->f = stderr;
#else
    u.pp = print_param_err;
    u.ppf->f = stderr;
#endif
}

/*
DEM red1 (DEM x);
DEM redu (DEM x);
DEM redu1 (DEM x);
*/

map ()
{
FILE *mf;

	mf = fopen ("lcei.map", "a");
	if (mf == NULL)
	{
		printf ("Impossible d'ouvrir le fichier map\n");
		perror ("fopen");
		return 0;
	}
#ifdef VAX_C
#define mfn(f) fprintf (mf, "%4X %s\n", f, "f");
#else
#define mfn(f) fprintf (mf, "%4X " #f "\n", f);
#endif
	mfn (print_dem);
	mfn (init_print_global);
	mfn (break_debug);
        mfn (red1); 
        mfn (redu);
        mfn (redu1);
        mfn (left);
        mfn (right);
        mfn (transym);
        mfn (sym);
        mfn (trans);
        mfn (mk_dem);
        mfn (init);
        mfn (printf);
        mfn (strncpy);
 	fclose (mf);
}

#ifdef CPP
lcei
#else
main
#endif
()
{
DEM d, ford, tford, f, n, p, nrtxf, limford, tlimford, q, limford1, r, n1, g,
 x, omega_suc, t_omega_suc;
struct
#ifdef CPP
        print_param
#else
        print_param_file
#endif
                print_param[1];
DEM t[30];
extern int trace;
char buf[10];
DEM l;
int i, c;
extern DEM defined_dems[0x100];
union
{
    struct print_param_file *ppf;
    struct print_param *pp;
} u;

    printf ("LCEI\n");
    map ();

    trace = 1;

    global ();

#ifdef CPP
    (void *)
#endif
        (print_param->print_string_param) =
#ifdef CPP
        (void *)
#endif
                print_string_file;
#ifndef CPP
    print_param->f = stdout;
#else
    u.pp = print_param;
    u.ppf->f = stdout;
#endif
    print_string (print_param, "Bonjour\n");

    init_print_global ();
    
    printf ("Initializing...\n");

    init ();

/*
    printf ("Initialized\n");
    gets (buf);
*/

    for (i=0; i<0x100; i++)
	defined_dems[i] = I;

    for (;;)
    {
        nnr = 0;
	print_string (print_param, "\nName  ? ");
        /* do c = readchar (); while (c == '\n'); */
        c = 'x';
        n = read_dem ();
        if (!strncmp(name(n), "TRA", 3))
        {
            flag_trace = 1;
            continue;
        } 
#ifdef TRACE1
        trace_dem ("", n);
#endif
	print_string (print_param, "Dem   ? ");
	d = read_dem ();
        trace_dem ("read", d);
        if (feof(stdin))
                break;
	defined_dems[c] = d;
        trace_dem ("", n);
        trace_dem ("", subdem(0,n));
        print_string (print_param, "\nName  : ");
        print_dem (print_param, n);
        if (node(n) == _Sym)
        {
#ifdef TRACE
                printf ("\nDefine symbol ");
                trace_dem ("value", d);
#endif
                subdem(0,n) = d;
                /* strcpy (name(d), name(n)); */
        }
#ifdef TRACE
        else
            printf ("\nNot symbol: %d ", node(n));
#endif
#ifndef ALLOC
        fprintf (stderr, "\n[%s] defined ", name(n));
#endif
        trace_dem ("", n);
        trace_dem ("", subdem(0,n));
        /* if (!strcmp (name(n), "MapDemL") || !strcmp (name(n), "MapDemR")) */
	{
	print_string (print_param, "\nDem   : ");
	print_dem (print_param, d);
	print_string (print_param, "\nLeft  : ");
#ifdef TRACE
        printf ("\nbefore left %x %x %x %x ",
                print_param,
                &((struct print_param_file *)print_param)->f,
                ((struct print_param_file *)print_param)->f,
                *(int *)0xFFDA
                );

#endif
        l = left (d);
#ifdef TRACE
        printf ("\nafter left %x %x %x %x ",
                print_param,
                &((struct print_param_file *)print_param)->f,
                ((struct print_param_file *)print_param)->f,
                *(int *)0xFFDA
                );
#endif
	print_dem (print_param, l);
#ifdef TRACE
        printf ("\nafter print_dem %x %x",
                print_param->print_string_param,
                print_string_file
                );
#endif
	print_string (print_param, "\nRight : ");
	r = right (d);
	print_dem (print_param, r);
        /* gets (buf); */ 
	}
	print_string (print_param, "\n");
        if (node(n) == _Sym)
                strcpy (name(d), name(n)); 

    }
#ifdef ALLOC
    free1 (dems); 
    while (!kbhit()); 
#endif    
#if 0
    printf ("%d\n", inclus (Fott(2,Ord,U(2)), Fott(3,Ord,U(2))));

    d = left (mk_dem (_defI, 3, NULL, U(5), K(2), NULL, NULL, NULL, NULL));
    print_dem (print_param, d);

    d = typ (I(30));
    print_dem (print_param, d);    
/*
    d = typ (K(40));
    print_dem (print_param, d);
*/
        
    f = Var ("f", Fott (Order(2), Ord, U(Order(1))));
    n = Var ("n", Ord);
    p = Var ("p", Ord);
    nrtxf = Var ("nrtxf", Ord);
        /*
        ford = ap (Y(fnc(ORD,TYPE)), lambda (f, lambda (n,
                ap (ap (ap (ap (TEST, ap (K(TYPE,ORD), TYPE)), n), T_ORD),
                        lambda (p, ap (ap (T_FNC, ap (f, p)), ap (f, p)))
                        ) )));
        */

/*
    ford = ap (Yt(Order(1),Fott(Order(2),Ord,U(Order(1)))), lambda (f, 
	    lambda (n,
             ap (ap (ap (Testt(Kottx(Order(2),U(Order(2)),Ord,U(Order(1)))),
		n), Ord), 
		    lambda (p, Fott (Order(1), ap (f, p), ap (f, p))) ) ) ));
*/

    t[1] = Fott (Order(1), ap(f,p), ap(f,p));
    print_string (print_param, "t[1] = ");
    print_dem (print_param, t[1]);

    t[2] = lambda (p, t[1]);
    print_string (print_param, "\nt[2] = ");
    print_dem (print_param, t[2]);

    t[3] = Testt (Kottx (Order(2), U(Order(2)), Ord, U(Order(1))));
    print_string (print_param, "\nt[3] = ");
    print_dem (print_param, t[3]);

    t[4] = ap (ap (ap (t[3], n), Ord), t[2]);
    print_string (print_param, "\nt[4] = ");
    print_dem (print_param, t[4]);

    /* trace = 1; */ 
    
    t[5] = lambda (n, t[4]);
    print_string (print_param, "\nt[5] = ");
    print_dem (print_param, t[5]);

    gets (buf);

    t[6] = lambda (f, t[5]);
    print_string (print_param, "\nt[6] = ");
    print_dem (print_param, t[6]);

    t[7] = Yt (Order(1), Fott (Order(2), Ord, U(Order(1))));
    print_string (print_param, "\nt[7] = ");
    print_dem (print_param, t[7]);

    t[8] = ap (t[7], t[6]);
    
    ford = t[8];    
      
    /* tford = typ (ford); */

    print_string (print_param, "\nford = ");
    print_dem (print_param, ford);

    tford = typ (ford);

    print_string (print_param, "\ntford = ");
    print_dem (print_param, tford);
    print_string (print_param, "\n");

    q = Var ("q", Ord);
    tlimford = PItt (Ord, lambda (q, Ftt (Ftt (Ord, ap (ford,q)),
                                         ap(ford,q) )));
    print_string (print_param, "\ntlimford = ");
    print_dem (print_param, tlimford);
    print_string (print_param, "\n");

    limford1 = Var ("limford1", tlimford);
    r = Var ("r", Ord);
    n1 = Var ("n1", Ord);
    f = Var ("f", Ftt (Ord, ap (ford, ap (Suc, n1))));
    g = Var ("g", ap (ford, n1));

    limford = ap (Yt(Order(1),tlimford), lambda (limford1,
                lambda (n, ap (ap (ap (Testt (
                    lambda (r, Ftt (Ftt (Ord, ap(ford,r)), ap(ford,r))) ),
                        n), Lim),
                            lambda (n1, lambda (f, lambda (g,
                                ap (ap (limford1, n),
                                    lambda (p, ap (ap (f, p), g))
                                   ) ))) )) ));

    print_string (print_param, "\nlimford = ");
    print_dem (print_param, limford);
    print_string (print_param, "\n");

    f = Var ("f", ap (ford, ap (Suc, n)));
    x = Var ("x", ap (ford, n));

    omega_suc = lambda (n, lambda (f, lambda (x,
        ap (ap (limford, n),
                lambda (p, ap (ap (ap (Rept(ap(ford,n)),
                        p), f), x)) ) )));

    print_string (print_param, "\nomega_suc = ");
    print_dem (print_param, omega_suc);

    t_omega_suc = typ (omega_suc);
    print_string (print_param, "\ntype      = ");
    print_dem (print_param, t_omega_suc);
    print_string (print_param, "\n");

#endif


}

