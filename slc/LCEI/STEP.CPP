
#include "lctm.h"

int length1 (DEM l)
{
    if (node(l) != _cons)
        return 0;
    return 1 + length1 (subdem(1,l));
}

int length (DEM l)
{
int n;
    n = length1 (l);
/*
    print_strint (print_param, "\nlength %d ", n);
    print_dem (print_param, l);
*/
}

DEM list_ap (DEM x, DEM s)
{
    if (node(x) != _ap)
        return cons (x, s);
    return list_ap (subdem(0,x), cons (subdem(1,x), s));
}

DEM ap_list (DEM f, DEM l)
{
    if (l == nil)
        return f;
    return ap_list (ap (f, subdem(0,l)), subdem(1,l));
}

DEM step (DEM x);
DEM rstep (DEM x);

int eq (DEM x, DEM y)
{
    return x==y;
}

int eq_node (DEM x, DEM y)
{
    return node(x) == node(y);
}

DEM step_list (DEM l1) 
{
DEM l, x;
    trace_dem ("step_list", l1);
    l = subdem(1,l1);
    switch (node(subdem(0,l1)))
    {
        case _I: return l;
        case _K: 
            if (length(l) < 2)
            {
                /* fprintf (stderr, "Stack underflow in K\n"); */
                return NULL;
            }
            return cons (subdem(0,l), subdem(1,subdem(1,l)));
        case _S: 
            if (length(l) < 3)
            {   
                /* fprintf (stderr, "Stack underflow in S\n"); */
                return NULL;
            }
            return cons (subdem(0,l), 
                         cons (subdem(0,subdem(1,subdem(1,l))),
                          cons (step(ap(subdem(0,subdem(1,l)),
                                        subdem(0,subdem(1,subdem(1,l))) )),
                           subdem(1,subdem(1,subdem(1,l))) ) ) );
        
/*        case _itransym:
            return cons (subdem(0,l),
                    cons (transym(subdem(0,subdem(1,l)),
                                  subdem(0,subdem(1,ssubdem(1,l))) ),
                          subdem(1,subdem(1,subdem(1,l))) ) );
  */
#define DEF_INSTR_1(_instr,funct) \
        case _instr: \
            if (length(l) < 2) \
            { \
                return NULL; \
           } \
            return cons (subdem(0,l), \
                    cons (funct(subdem(0,subdem(1,l))), \
                     subdem(1,subdem(1,l)) ) );

#define DEF_INSTR_2(_instr,funct) \
        case _instr: \
            if (length(l) < 3) \
            { \
                return NULL; \
            } \
            return cons (subdem(0,l), \
                    cons (funct(subdem(0,subdem(1,l)), \
                                subdem(0,subdem(1,subdem(1,l))) ), \
                          subdem(1,subdem(1,subdem(1,l))) ) );

        DEF_INSTR_2 (_itransym, transym)

        DEF_INSTR_1 (_idefI, defI)
        DEF_INSTR_2 (_idefK, defK)
        /* case _idefK:
            return cons (subdem(0,l), 
                    cons (defK(subdem(0,subdem(1,l)),
                               subdem(0,subdem(1,subdem(1,l))) ),
                     subdem(1,subdem(1,subdem(1,l))) ) ); */
        case _idefS:
            return cons (subdem(0,l),
                    cons (defS(subdem(0,subdem(1,l)),
                               subdem(0,subdem(1,subdem(1,l))),
                               subdem(0,subdem(1,subdem(1,subdem(1,l)))) ),
                     subdem(1,subdem(1,subdem(1,subdem(1,l)))) ) );

#define DEF_INSTR_TEST(_instr,test) \
        case _instr: \
            if (length(l) < 5) \
            { \
                return NULL; \
            } \
            if (subdem(0,subdem(1,subdem(1,subdem(1,l)))) == \
                subdem(0,subdem(1,subdem(1,subdem(1,subdem(1,l))))) ) \
                x = subdem(0,l); \
            else \
                x = subdem(0,subdem(1,l)); \
            return cons (x, cons (subdem(0,subdem(1,subdem(1,l))), \
                    subdem(1,subdem(1,subdem(1,subdem(1,subdem(1,l))))) ));

        DEF_INSTR_TEST (_ieq, eq)
        DEF_INSTR_TEST (_inode, eqnode)

        DEF_INSTR_1 (_ileft, left)
        DEF_INSTR_1 (_iright, right)
        DEF_INSTR_1 (_ired, red)
        DEF_INSTR_1 (_iredu, redu)
        DEF_INSTR_2 (_iext, ext)
        DEF_INSTR_1 (_istep, step)
        DEF_INSTR_1 (_irstep, rstep)

        default:
            fprintf (stderr, "Undefined instruction %d\n", 
                     node(subdem(0,l1)) );
            return l1;
        
    }

}

DEM step (DEM x)
{
DEM l, l1;
    if (node(x) != _ap)
        return x;
    l = list_ap (x, nil);
    l1 = step_list (l);
    if (l1 == NULL)
        return x;
    return ap_list (subdem(0,l1), subdem(1,l1));
}

DEM rstep (DEM x)
{
DEM y;
    for (;;)
    {
        trace_dem ("step", x);
        y = step (x);
        if (y == x)
            return x;
        /* trace_dem ("step", y); */
        x = y;
    }    
}

