
#include "lctm.h"
#include "conio.h"

extern int trace;

struct frame
{
    char *fnc;
    DEM arg[3];
};

int sp = 0;
struct frame stack[300];

push (char *fnc, DEM arg0, DEM arg1, DEM arg2)
{
int trace1;
    stack[sp].fnc = fnc;
    stack[sp].arg[0] = arg0;
    stack[sp].arg[1] = arg1;
    stack[sp].arg[2] = arg2;
    sp++;  
    trace1 = trace;
    trace = 1;  
    trace_stack (print_param);
    trace = trace1;
}

void pop (void)
{
    sp--;
}

trace_stack (struct print_param *p)
{
int l, i;
char buf[10];
    return 0;
    gotoxy (1, 1);
    print_strint (p, "%d levels", sp);
    clreol ();
    print_string (p, "\n");
    clreol ();

    for (l=((sp<=4)?0:(sp-4)); l<sp; l++)
    /* for (l=0; (sp<=5)?(l<sp):(l<5); l++) */
    {
        print_strint (p, "\nLevel %d : ", l);
        print_string (p, stack[l].fnc);
        for (i=0; i<3; i++)
        {
            clreol ();
            if (stack[l].arg[i] != NULL)
            {
                print_strint (p, "\n\targ%d = ", i);
                print_dem (p, stack[l].arg[i]);
            }
            clreol ();            
        }
        print_string (p, "\n");
        clreol ();
    }
    print_string (p, "*******\n");
    clreol ();
    /* gets (buf); */    
}

