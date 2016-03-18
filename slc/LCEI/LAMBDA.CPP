
#include "lctm.h"

/*  
let rec lambda z = function
	z -> let a = typ z in
	     let u = typ a in
	     let o = pred_order (order_u u) in
	     Iot o a
      |	ap (xz, yz) -> 
	     let a = typ z in
	     let u = typ a in
	     let o = pred_order (order_u u) in
	     let bz = typ yz in
	     let b = fnc bz in
	     let PIbzcz = typ xz in
	     let cz = arg PIbzcz in
	     let c = fnc cz in
	     Sotttxx o a b c (lambda z xz) (lambda z yz)
      | x -> let a = typ z in
	     let b = typ x in
	     let u = typ a in
	     let o = pred_order (order_u u) in
	     Kottx o b a x
*/

DEM lambda1 (DEM z, DEM r)
{
DEM l, a, b;
    if (z == r)
        return I;
    else if (!in (z, r))
        return ap (K, r);
    else if (node(r) == _ap)
    {
        if (subdem(1,r) == z && !in (z, subdem(0,r)))
            return subdem(0,r);
        else
        {
            /*
            return ap (ap (S, lambda1 (z, subdem(0,r))),
                              lambda1 (z, subdem(1,r))); */
            a = lambda1 (z, subdem(0,r));
            b = lambda1 (z, subdem(1,r));
            l = ap (ap (S, a), b);
            return l;
        }
    }
    else
        error ("lambda: bad result", __FILE__, __LINE__, r);
}

DEM lambda1t (DEM z, DEM r)
{
#if 1
    return Lambda (z, r);
#else
DEM a, b, c, u, v, w, bz, cz, PIbzcz, bz1, tf, tf1, r1;
ORDER o, o1;
    if (z == r)
    {
	a = typ(z);
	return Iot (pred_order (order_u (typ (a))), a);
    }
    else if (!in (z, r))
    {
        a = typ (z);
        b = typ (r);
        u = typ (a);
        v = typ (b);
        w = unio (u, v);
        return Kottx (pred_order (order_u(w)), b, a, r);
    }
    else if (node(r) == _ap)
    {
        if (subdem(1,r) == z && !in (z, subdem(0,r)))
            return subdem(0,r);
        a = typ (z);
        u = typ (a);
        bz = typ (subdem(1,r));
        /* b = fnc (bz); */
        b = lambda (z, bz);
        /*PIbzcz = typ (subdem(0,r));
          cz = arg (PIbzcz);*/
        tf = typ (subdem(0,r));
#if 1
	cz = typ_ap (r);
	if (cz == NULL)
	    error ("Bad type of function in lambda", __LINE__, tf); 
	goto re;
#else
    new_tf:
	if (node(tf) == _ap &&
            node(subdem(0,tf)) == _ap)
        {
            if (node(subdem(0,subdem(0,tf))) == _F)
            {
                o = order(subdem(0,subdem(0,tf)));
                bz1 = subdem(1,subdem(0,tf)); 
                cz = Kottx (suc_order(o), U(o), bz1, subdem(1,tf));
                goto re;

            }
            else if (node(subdem(0,subdem(0,tf))) == _PI)
            {
                cz = arg (tf);
                goto re;
            }
        }
	/* r1 = ap (simplif (subdem(0,r)), subdem(1,r));
        if (r1 != r) */
	tf1 = simplif (tf);
	if (tf1 != tf)
	    /*return lambda (z, r1);*/
        {
            tf = tf1;
            goto new_tf; 
        }
        error ("Bad type of function in lambda", __LINE__, tf); 
	/* c = fnc (cz); */
        /*c = lambda (z, cz);*/
#endif
    re:
        c = lambda (z, cz);
        o1 = max_order (order_u(u), max_order (order_u(typ(bz)), 
           order_u(typ(tf)) ));                                     

	return Sotttxx (pred_order (o1/*order_u (u)*/), a, b, c,
	    lambda (z, subdem(0,r)), 
	    lambda (z, subdem(1,r)));
    }
    else
    {
        error ("lambda: bad result", __LINE__, r);

/*
	a = typ (z);
	b = typ (r);
	u = typ (a);
        return Kottx (pred_order (order_u(u)), b, a, r);
*/
    }
#endif
}
