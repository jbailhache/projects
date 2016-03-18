
#include "lctm.h"

DEM typ (DEM x)
{
DEM t;
    print_string (print_param, "call type of ");
    print_dem (print_param, x);
    print_string (print_param, "\n");
    
    push ("typ", x, NULL, NULL);  
    t = typ1 (x);
    pop (); 

    print_string (print_param, "result type of ");
    print_dem (print_param, x);
    print_string (print_param, " is ");
    print_dem (print_param, t);
    print_string (print_param, "\n");

    return t;
}

/* DEM lambda1 (DEM z, DEM r); */

DEM lambda0 (char *file, int line, DEM z, DEM r)
{
DEM l;
char buf[300];
/*
    sprintf (buf, "%s(%d)\ncall lambda ", file, line);
    print_string (print_param, buf);
    print_dem (print_param, z);
    print_string (print_param, " ");
    print_dem (print_param, r);
    print_string (print_param, "\n");
*/
    push ("lambda", z, r, NULL);
    l = lambda1 (z, r);
    pop ();
/*
    sprintf (buf, "%s(%d)\nresult lambda ", file, line);
    print_string (print_param, buf);
    print_dem (print_param, z);
    print_string (print_param, " ");
    print_dem (print_param, r);
    print_string (print_param, " = ");
    print_dem (print_param, l);
    print_string (print_param, "\n");
*/
    return l;
}

DEM simplify (DEM x);

DEM simplif (DEM x)
{
DEM y;
char buf[10];

    print_string (print_param, "call simplif ");
    print_dem (print_param, x);
    print_string (print_param, "\n");

    push ("simplif", x, NULL, NULL); 
    y = simplify (x);
    pop (); 

    print_string (print_param, "result simplif ");
    print_dem (print_param, x); 
    print_string (print_param, " = ");
    print_dem (print_param, y);
    print_string (print_param, "\n");

    /* gets (buf); */

    return y;
}
