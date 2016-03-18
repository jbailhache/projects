
#include "lctm.h"

DEM subst (DEM a, DEM v, DEM x);

DEM subst1 (DEM a, DEM v, DEM x)
{
    if (x == v)
        return a;
    if (node(x) == _ap)
        return ap (subst (a, v, subdem(0,x)),
                   subst (a, v, subdem(1,x)));
    if (node(x) == _Lambda && subdem(0,x) != v)
        return Lambda (subdem(0,x), subst (a, v, subdem(1,x)));
    return x;    
}

DEM subst (DEM a, DEM v, DEM x)
{
DEM r;
/*
    print_string (print_param, "\nSubst a = ");
    print_dem (print_param, a);
    print_string (print_param, "\nsubst v = ");
    print_dem (print_param, v);
    print_string (print_param, "\nsubst x = ");
    print_dem (print_param, x);
*/
    r = subst1 (a, v, x);
/*
    print_string (print_param, "\nsubst a = ");
    print_dem (print_param, a);
    print_string (print_param, "\nsubst v = ");
    print_dem (print_param, v);
    print_string (print_param, "\nsubst x = ");
    print_dem (print_param, x);
    print_string (print_param, "\nsubst r = ");
    print_dem (print_param, r);
*/
    return r;
}

DEM simplif1 (DEM x)
{
int dp;
DEM k1, k2, pi, b;
ORDER o;
#if 1
    dp = depth_l (x);
    print_strint (print_param, "dp = %d\n", dp);
    switch (dp)
    {
        /*
        case 0 :
        case 1 :
            return x;
        */
	case 1 :
	    if (node(subdem(0,x)) == _It)
		return subdem(1,x);
	    return x;

	case 2 :
            if (node(subdem(0,subdem(0,x))) == _IT)
		return subdem(1,x);
	    if (node(subdem(0,subdem(0,x))) == _Kt)
		return subdem(1,subdem(0,x));
            /* S (K(Ka)) b = Ka */
            if (node(subdem(0,subdem(0,x))) == _St &&
                node(subdem(1,subdem(0,x))) == _ap &&
                node(k1=subdem(0,subdem(1,subdem(0,x)))) == _Kt && 
                node(subdem(1,subdem(1,subdem(0,x)))) == _ap &&
                node(k2=subdem(0,subdem(1,subdem(1,subdem(0,x))))) == _Kt)     
            {
                o = max_order (order(k1), order(k2));
                return Kottx (o, subdem(0,k2), subdem(1,k1), 
                       subdem(1,subdem(1,subdem(1,subdem(0,x)))));             
            }
            /* PI a (Kb) = F a b */
            if (node(pi=subdem(0,subdem(0,x))) == _PI &&
                node(subdem(1,x)) == _ap &&
                node(subdem(0,subdem(1,x))) == _Kt)
                return Fott (order(pi), subdem(1,subdem(0,x)),
                       subdem(1,subdem(1,x)));
            if (node(pi=subdem(0,subdem(0,x))) == _PI &&
                node(b=subdem(1,x)) == _Lambda &&
                !in(subdem(0,b),subdem(1,b)))
                return Fott (order(pi), subdem(1,subdem(0,x)),
                        subdem(1,b));
            if (node(subdem(0,x)) == _Lambda)
            {
                print_string (print_param, "_Lambda\n");
                return subst (subdem(1,x), subdem(0,subdem(0,x)),
                        subdem(1,subdem(0,x)));
            }
            print_string (print_param, "return x\n");
	    return x;

	case 3 :
	    if (node(subdem(0,subdem(0,subdem(0,x)))) == _St)
		return ap (ap (subdem(1,subdem(0,subdem(0,x))),
		               subdem(1,x)),
			   ap (subdem(1,subdem(0,x)),
			       subdem(1,x)));
	    return x;
	    
	case 4 :
            if (node(subdem(0,subdem(0,subdem(0,subdem(0,x))))) == _KT)
		return subdem(1,subdem(0,x));
	    return x;

	case 6 :
	    if (node(subdem(0,subdem(0,subdem(0,subdem(0,subdem(0,
                    subdem(0,x))))))) == _ST)
		return ap (ap (subdem(1,subdem(0,subdem(0,x))),
		               subdem(1,x)),
			   ap (subdem(1,subdem(0,x)),
			       subdem(1,x)));
            return x;

	default :
	    return x;
    }
#endif
}

DEM simplif2 (DEM x)
{
DEM y;
    y = simplif1 (x);
    if (y != x)
        return y;
    if (node(x) == _ap)
        return ap (simplif2 (subdem(0,x)), simplif2 (subdem(1,x)));
    if (node(x) == _Lambda)
        return Lambda (subdem(0,x), simplif2(subdem(1,x)));
    return x;
}

/*
DEM simplif3 (DEM x)
{
DEM y;
    y = simplif2 (x); 

}
*/

DEM simplify (DEM x)
{
    return simplif2 (x);
}
