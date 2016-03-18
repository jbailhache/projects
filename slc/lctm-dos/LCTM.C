
#include "lctm.h"

struct print_param_file print_param_err[1];

error (char *s, int line, DEM d)
{
    fprintf (stderr, "Error at line %d : %s ", line, s);
    print_dem (print_param_err, d);
    exit (1);
}

init_print_global ()
{
/* FILE *nul;
    nul = fopen ("NUL:", "w"); */
    print_param->print_string_param = print_string_nul;

    print_param_err->print_string_param = print_string_file;
    print_param_err->f = stderr;
}

main ()
{
DEM d, ford, tford, f, n, p, nrtxf;
struct print_param_file print_param[1];

    global ();

    print_param->print_string_param = print_string_file;
    print_param->f = stdout;
    print_string (print_param, "Bonjour\n");

    init_print_global ();

    init ();

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

    ford = ap (Yt(Order(1),Fott(Order(2),Ord,U(Order(1)))), lambda (f, 
	    lambda (n,
	     ap (ap (ap (Testt(Kottx(Order(1),U(Order(2)),Ord,U(Order(1)))),
		n), Ord), 
		    lambda (p, Fott (Order(1), ap (f, p), ap (f, p))) ) ) ));
      
    tford = typ (ford);

    print_string (print_param, "ford = ");
    print_dem (print_param, ford);
    print_string (print_param, "\ntford = ");
    print_dem (print_param, tford);
    print_string (print_param, "\n");
    
}

