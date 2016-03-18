
#include "lctm.h"

DEM typ (DEM x)
{
DEM t;
    print_string (print_param, "call type of ");
    print_dem (print_param, x);
    print_string (print_param, "\n");
    
    t = typ1 (x);

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
    sprintf (buf, "%s(%d)\ncall lambda ", file, line);
    print_string (print_param, buf);
    print_dem (print_param, z);
    print_string (print_param, " ");
    print_dem (print_param, r);
    print_string (print_param, "\n");

    l = lambda1 (z, r);

    sprintf (buf, "%s(%d)\nresult lambda ", file, line);
    print_string (print_param, buf);
    print_dem (print_param, z);
    print_string (print_param, " ");
    print_dem (print_param, r);
    print_string (print_param, " = ");
    print_dem (print_param, l);
    print_string (print_param, "\n");

    return l;
}

DEM simplify (DEM x);

DEM simplif (DEM x)
{
DEM y;

    print_string (print_param, "call simplif ");
    print_dem (print_param, x);
    print_string (print_param, "\n");

    y = simplify (x);

    print_string (print_param, "result simplif ");
    print_dem (print_param, x); 
    print_string (print_param, " = ");
    print_dem (print_param, y);
    print_string (print_param, "\n");

    return y;
}
