
#include "lctm.h"

/*

let rec left = function
      Var (n, t) -> Var (n, t)
    | I o -> I o
    | K o -> K o
    | S o -> S o
    | Y o -> Y o
    | PI o -> PI o
    | U o -> U o
    | ap (d1, d2) -> ap (left d1, left d2)
    | transym (d1, d2) -> right d1 
    | defI (o, d1) -> ap (I o, left d1)
    | defK (o, d1, d2) -> ap (ap (K o, left d1), left d2)
    | defS (o, d1, d2, d3) -> ap (ap (ap (S o, left d1), left d2), left d3)
*/

/* DEM right (DEM d); */

DEM left (DEM d)
{
    switch (node(d))
    {
        case _ap:
             return ap (left(subdem(0,d)), left(subdem(1,d))); 
        case _transym:
             return right (subdem(0,d));
        case _defI:
             return ap (I(order(d)), left(subdem(1,d)));
        case _defK:
             return ap (ap (K(order(d)), left(subdem(2,d))),
                                         left(subdem(3,d)));
        case _defS:
             return ap (ap (ap (S(order(d)), left(subdem(3,d))),
                                             left(subdem(4,d))),
                                             left(subdem(5,d)));
	case _It:
	    return It (order(d), left(subdem(0,d)));
	case _Kt:
	    return Kt (order(d), left(subdem(0,d)), left(subdem(1,d)));
	case _St:
	    return St (order(d), left(subdem(0,d)),
		                 left(subdem(1,d)),
				 left(subdem(2,d)));
	case _Yt:
	    return Yt (order(d), left(subdem(0,d)));
	
	case _Rept:
	    return Rept (/* order(d), */left(subdem(0,d)));
	case _Testt:
	    return Testt (left(subdem(0,d)));

        default:
             return d;
    }
}

/*
and right = function
      Var (n, t) -> Var (n, t)
    | I o -> I o
    | K o -> K o
    | S o -> S o
    | Y o -> Y o
    | PI o -> PI o
    | U o -> U o
    | ap (d1, d2) -> ap (right d1, right d2)
    | transym (d1, d2) -> right d2
    | defI (o, d1) -> right d1
    | defK (o, d1, d2) -> right d1
    | defS (o, d1, d2, d3) -> ap (ap (right d1, right d3), ap (right d2, right 
d3));;
*/

DEM right (DEM d)
{
    switch (node(d))
    {
        case _ap:
             return ap (right(subdem(0,d)), right(subdem(1,d)));
        case _transym:
             return right (subdem(1,d));
        case _defI:
             return right (subdem(1,d));
        case _defK:
             return right (subdem(2,d));
        case _defS:
             return ap (ap (right(subdem(3,d)), right(subdem(5,d))),
                        ap (right(subdem(4,d)), right(subdem(5,d))));
	case _It:
	    return It (order(d), right(subdem(0,d)));
	case _Kt:
	    return Kt (order(d), right(subdem(0,d)), right(subdem(1,d)));
	case _St:
	    return St (order(d), right(subdem(0,d)),
		                 right(subdem(1,d)),
				 right(subdem(2,d)));
	case _Yt:
	    return Yt (order(d), right(subdem(0,d)));

	case _Rept:
	    return Rept (right(subdem(0,d)));
	case _Testt:
	    return Testt (right(subdem(0,d)));

        default:
             return d;
    }
} 

