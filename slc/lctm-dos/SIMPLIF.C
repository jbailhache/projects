
#include "lctm.h"

DEM simplif1 (DEM x)
{
int dp;
DEM k1, k2, pi;
ORDER o;
    dp = depth (x);
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
	    if (node(subdem(0,subdem(0,x))) == _I)
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

	    return x;

	case 3 :
	    if (node(subdem(0,subdem(0,subdem(0,x)))) == _St)
		return ap (ap (subdem(1,subdem(0,subdem(0,x))),
		               subdem(1,x)),
			   ap (subdem(1,subdem(0,x)),
			       subdem(1,x)));
	    return x;
	    
	case 4 :
	    if (node(subdem(0,subdem(0,subdem(0,subdem(0,x))))) == _K)
		return subdem(1,subdem(0,x));
	    return x;

	case 6 :
	    if (node(subdem(0,subdem(0,subdem(0,subdem(0,subdem(0,
		    subdem(0,x))))))) == _S)
		return ap (ap (subdem(1,subdem(0,subdem(0,x))),
		               subdem(1,x)),
			   ap (subdem(1,subdem(0,x)),
			       subdem(1,x)));
            return x;

	default :
	    return x;
    }

}

DEM simplif2 (DEM x)
{
DEM y;
    y = simplif1 (x);
    if (y != x)
        return y;
    if (node(x) != _ap)
        return x;
    return ap (simplif2 (subdem(0,x)), simplif2 (subdem(1,x)));
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
