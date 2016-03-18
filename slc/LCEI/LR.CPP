
#include "lctm.h"

#define TR /* printf ("\n%d: %x ", __LINE__, *(int *)0xFFDA); */

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

test_EA (DEM d, DEM *l, DEM *r)
{
DEM ld, rd;
    ld = left (d);
    rd = right (d);
    if (node(ld) != _ap)
        return 0;
    if (node(subdem(0,ld)) != _ap)
        return 0;
    if (node(subdem(0,subdem(0,ld))) != _E)
        return 0;
    if (node(rd) != _I)
        return 0;
    *l = subdem(1,subdem(0,ld));
    *r = subdem(1,ld);
    return 1;
}

/* S(S(KE)a)b = KI */
test_EXT (DEM d, DEM *l, DEM *r)
{
DEM ld, rd, t[10];
    ld = left (d);
    rd = right (d);
    if (node(ld) != _ap)
        return 0;
    t[1] = subdem(0,ld);
    if (node(t[1]) != _ap)
        return 0;
    if (node(subdem(0,t[1])) != _S)
        return 0;
    t[2] = subdem(1,t[1]);
    if (node(t[2]) != _ap)
        return 0;
    t[3] = subdem(0,t[2]);
    if (node(t[3]) != _ap)
        return 0;
    if (node(subdem(0,t[3])) != _S)
        return 0;
    t[4] = subdem(1,t[3]);
    if (node(t[4]) != _ap)
        return 0;
    if (node(subdem(0,t[4])) != _K)
        return 0;
    if (node(subdem(1,t[4])) != _E)
        return 0;
    *l = subdem(1,t[2]);
    *r = subdem(0,ld);
    return 1;        
}

DEM left1 (DEM d)
{
DEM l, r, d1;
int status;
    switch (node(d))
    {
        case _ap:
             return ap (left(subdem(0,d)), left(subdem(1,d))); 
        case _transym:
             if (left(subdem(0,d)) == left(subdem(1,d)))   
                return right (subdem(0,d));
             return I;
/*
        case _defI:
             return ap (I(order(d)), left(subdem(1,d)));
        case _defK:
             return ap (ap (K(order(d)), left(subdem(2,d))),
                                         left(subdem(3,d)));
        case _defS:
             return ap (ap (ap (S(order(d)), left(subdem(3,d))),
                                             left(subdem(4,d))),
*/
        case _defI:
             return ap (I, left(subdem(0,d)));
        case _defK:
             return ap (ap (K, left(subdem(0,d))),
                                         left(subdem(1,d)));
        case _defS:
             return ap (ap (ap (S, left(subdem(0,d))),
                                             left(subdem(1,d))),
                                             left(subdem(2,d)));
                
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

	case _Ext1: return l_Ext1;
	case _Ext2: return l_Ext2;
	case _Ext3: return l_Ext3;
	case _Ext4: return l_Ext4;
	case _Ext5: return l_Ext5;
	case _Ext6: return l_Ext6;

        case _AE:
            return SEI;

        case _EA0:
            return l_EA0;

        case _EA:
            status = test_EA (d, &l, &r);
            if (status)
                return l;
            return I;

        case _EXT:
            status = test_EXT (d, &l, &r);
            if (status)
                return l;
            return I;

        case _MP:
            return IfI;

        case _AI:
            return SIfI;

        case _AK:
            return SKSIfIf;

        case _AS:
            return l_AS;

        case _RPA:
            return l_RPA;

	case _ZeroIsOrd:    return l_ZeroIsOrd;
	case _SucIsOrd:	    return l_SucIsOrd;
	case _LimIsOrd:	    return l_LimIsOrd;
	case _PredIsOrd:    return l_PredIsOrd;
	case _StepIsOrd:    return l_StepIsOrd;
        case _TfI:          return l_TfI;

        case _Axm:
            return subdem(0,d);
/*
        case _Sym:
            if (d->subdem(0) == NULL)
                return d;
            else
                return d->subdem(0);
*/
        case _Subst:
             return ap (Lambda (subdem(0,d), subdem(1,d)), subdem(2,d));

        case _DB_Subst:
             return ap (DBLambda (subdem(0,d)), subdem(1,d));

        case _Ext:
        /* case _Lambda: */
             trace_dem ("_Ext(0)", subdem(0,d));
             trace_dem ("_Ext(1)", subdem(1,d));   
             d1 = left (extens (subdem(0,d), left(subdem(1,d))));
             trace_dem ("_Ext(r)", d1);
             return d1;

        case _Lambda:
             return Lambda (subdem(0,d), left(subdem(1,d)));

        case _DBLambda:
             return DBLambda (left(subdem(0,d)));

        case _IfNode:
            return ap (ap (ap (E, left(subdem(0,d))), right(subdem(0,d))),
                        left(subdem(1,d)));

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

DEM right1 (DEM d)
{
DEM l, r;
int status;
    switch (node(d))
    {
        case _ap:
             return ap (right(subdem(0,d)), right(subdem(1,d)));
        case _transym:
             if (left(subdem(0,d)) == left(subdem(1,d)))   
                return right (subdem(1,d));
             return I;
/*
        case _defI:
             return right (subdem(1,d));
        case _defK:
             return right (subdem(2,d));
        case _defS:
             return ap (ap (right(subdem(3,d)), right(subdem(5,d))),
                        ap (right(subdem(4,d)), right(subdem(5,d))));
*/
        case _defI:
             return right (subdem(0,d));
        case _defK:
             return right (subdem(0,d));
        case _defS:
             return ap (ap (right(subdem(0,d)), right(subdem(2,d))),
                        ap (right(subdem(1,d)), right(subdem(2,d))));

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

	case _Ext1: return r_Ext1;
	case _Ext2: return r_Ext2;
	case _Ext3: return r_Ext3;
	case _Ext4: return r_Ext4;
	case _Ext5: return r_Ext5;
	case _Ext6: return r_Ext6;

        case _AE:
            return KI;

        case _EA0:
            return r_EA0;

        case _EA:
            status = test_EA (d, &l, &r);
            if (status)
                return r;
            return I;

        case _EXT:
            status = test_EXT (d, &l, &r);
            if (status)
                return r;
            return I;

        case _MP:
            return I;

        case _AI:
            return KI;

        case _AK:
            return KKI;

        case _AS:
            return KKKI;

        case _RPA:
            return KI;

	case _ZeroIsOrd:    return r_ZeroIsOrd;
	case _SucIsOrd:	    return r_SucIsOrd;
	case _LimIsOrd:	    return r_LimIsOrd;
	case _PredIsOrd:    return r_PredIsOrd;
	case _StepIsOrd:    return r_StepIsOrd;	
        case _TfI:          return r_TfI;

        case _Axm:
                return subdem(1,d);
/*
        case _Sym:
            if (d->subdem(0) == NULL)
                return d;
            else
                return d->subdem(0);
*/
        case _Subst:
             return subst (subdem(2,d), subdem(0,d), subdem(1,d));

        case _DB_Subst:            
#if 1
             return DBsubst (0, subdem(0,d), subdem(1,d));  
#else
             return dbshift (0, -1,
                 DBsubst (0, subdem(0,d), dbshift(0,1,subdem(1,d)))); 
#endif

        case _Ext:
        /* case _Lambda: */
             return right (extens (subdem(0,d), right(subdem(1,d))));

        case _Lambda:
             return Lambda (subdem(0,d), right(subdem(1,d)));

        case _DBLambda:
             return DBLambda (right(subdem(0,d)));


        case _IfNode:
            return ap (ap (ap (E, left(subdem(0,d))), right(subdem(0,d))),
                        right(subdem(1,d)));

        default:
             return d;
    }
}

DEM left (DEM d)
{
TR
    if (d->_left == NULL)
        d->_left = left1 (d);
TR
    return d->_left;
}

DEM right (DEM d)
{
    if (d->_right == NULL)
        d->_right = right1 (d);
    return d->_right;
}

