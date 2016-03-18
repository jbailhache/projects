
#include "lctm.h"

/* #define NULL ((void *)0) */

DEM prev = NULL;
DEM *watch = (void *)0;

int flag_trace = 0;

trace_dem1 (char *file, int line, char *s, DEM d, char *nd, int flag) 
{ 
char format[1000];
    if (flag_trace)
        flag = flag_trace;
    if (flag || flag_trace || (watch != NULL && *watch != prev))
    {
        sprintf (format, "\n%s(%d) %s : %s = %08lX \n dem :   ",
            file, line, s, nd, d); 
        print_string (print_param, format); 
        print_dem (print_param, d); 
        print_string (print_param, "\n left :  "); 
        print_dem (print_param, left(d)); 
        print_string (print_param, "\n right : "); 
        print_dem (print_param, right(d)); 
        /* printf ("\nwatch=%04X *watch=%04X prev=%04X\n",
                watch, *watch, prev); */
        if (watch != NULL && *watch != prev) 
        {
            print_string (print_param, "\nModified, old value: ");
            print_dem (print_param, prev);
            print_string (print_param, ", new value: ");
            print_dem (print_param, *watch);
        }
        /* gets (format); */
    }
    prev = *watch;
}

