
#include "lctm.h"

DEM typ1 (DEM x)
{
int o, o1, o2;
DEM a, b, c, c1, f, x1, y, z, v, PIab, bz, s, tf, tf1, tz, tz1, t, n, n1, r;
#if 1
	return U(Order(0));
#else

    o = order(x);
    o1 = suc_order(o);
    o2 = suc_order(o1);

    switch (node(x))
    {
	case _Var : return subdem(0,x);

	case _It:
	    a = subdem(0,x);
	    t = Fott (o1, a, a);
	    return t;

        case _IT :
	    a = Var ("a", U(o1)); 
	    return PIott (o2, U(o1), lambda (a,
			   Fott (/*suc_order*/(o1), a, a) ));

	case _Kt:
	    a = subdem(0,x);
	    b = subdem(1,x);
	    t =  Fott (o1, a, Fott (o1, b, a));
	    return t;

        case _KT :
	    a = Var ("a", U(o1));
	    b = Var ("b", U(o1));
	    return PIott (o2, U(o1), lambda (a,
		    PIott (o2, U(o1), lambda(b,
		     Fott (o1, a, Fott (o1, b, a)) )) ));

	case _St:
	    a = subdem(0,x);
            b = subdem(1,x);
	    c = subdem(2,x);
     z = Var ("z", a);
     y = Var ("y", PIott (o1, a, b));
	    t = Fott (o1, PIott (o1, a, lambda (z,
		        PIott(o1, ap(b,z),ap(c,z)))),
		         PIott (o1, PIott (o1, a, b), lambda (y, 
			  Fott (o1, a, ap(ap(c,z),ap(y,z)))) ));
	    return t;

        case _ST :
	    a = Var ("a", U(o1));
	    b = Var ("b", Fott (o2, a, U(o1)));
            z = Var ("z", a);
	    c = Var ("c", PIott (o1, a, lambda (z, Fott (o2, ap(b,z), U(o1)))));
	    y = Var ("y", PIott (o1, a, b));
	    
	    return PIott (o2, U(o1), lambda (a,
		    Fott (o2, Fott (o2, a, U(o1)), lambda (b,
		     PIott (o1, PIott (o1, a, lambda (z, 
		      Fott (o2, ap(b,z), U(o1)))), lambda (c, 
		       Fott (o1, PIott (o1, a, lambda (z,
		        PIott(o1, ap(b,z),ap(c,z)))),
		         PIott (o1, PIott (o1, a, b), lambda (y, 
			  Fott (o1, a, ap(ap(c,z),ap(y,z)))) )))
			    ) ))));

	case _Yt:
	    a = subdem(0,x);
	    t = Fott (o1, Fott (o1, a, a), a);
	    return t;

	case _Ord:
	    return U(Order(1));

	case _Zero:
	    return Ord;

	case _Suc:
	    return Fott (Order(1), Ord, Ord);

	case _Lim:
	    return Fott (Order(1), Fott (Order(1), Ord, Ord), Ord);

	case _Rept:
	    o1 = Order(1);
	    a = subdem(0,x);
	    t = Fott (o1, Ord, 
		    Fott (o1, Fott (o1, a, a), Fott (o1, a, a)));
	    return t;

	case _Testt:
	    o1 = Order(1);
	    a = subdem(0,x);
	    n = Var ("n", Ord);
            n1 = Var ("n1", Ord);
            t = PIott (o1, Ord, lambda (n1, Fott (o1, ap (a, Zero),
                    Ftt ( PIott (o1, Ord, lambda (n, ap (a, ap (Suc, n)))),
                           ap (a, n1) ) )));
	    return t;

        case _F:
            return Fott (o1, U(o), Fott (o1, U(o), U(o)));

	case _PI:
	    a = Var ("a", U(o));
	    return PIott (o1, U(o), lambda (a,
			    Fott (o1, Fott (o1, a, U(o)), U(o)) ));
		     
        case _U: return U (suc_order (order_u (x)));

	case _ap:
            if (depth(x) == 1 && node(s=rfnc(1,x)) == _Kt)
	    {
		a = subdem(0,s);
		b = subdem(1,s);
		o = order(s);
		return Fott (o, b, a);
            }
	    if (node(subdem(0,x)) == _ap &&
	        node(subdem(0,subdem(0,x))) == _ap &&
                node(subdem(0,subdem(0,subdem(0,x)))) == _KT)
	    {
		a = subdem(1,subdem(0,subdem(0,x)));
		b = subdem(1,subdem(0,x));
		o = order(a);
		return Fott (o, b, a);
	    }
	    if (depth (x) == 2 && node(s=rfnc(2,x)) == _St)
	    {
		a = subdem(0,s);
		b = subdem(1,s);
		c = subdem(2,s);
		goto Sabc;				
	    }
            if (depth (x) == 5 && node(s=rfnc(5,x)) == _ST)
	    {
	    /* S a:Uo+1 b:(Uo(a)+1) c:(a)>\z:a.((bz)>Uo+1) 
		 x:(a)>\z:a.(cz(bz)) y:(a)>b z:a = xz(yz):cz(yz)
		 xz:(bz)>cz, yz:bz
	       S a b c x y : a ->> \z:a. cz(yz)
             */
	        a = subdem(1,rfnc(4,x));
		b = subdem(1,rfnc(3,x));
		c = subdem(1,rfnc(2,x));
	    Sabc:
		x1 = subdem(1,rfnc(1,x));
		y = subdem(1,rfnc(0,x));
		z = Var ("z", a);
		o = order(s);
		o1 = suc_order (o);
		/* t = PIott (o1, a, lambda (z, ap (ap (c, z), ap (y, z)))); */
		v = Var ("v", simplif (ap (b, z)));
		c1 = lambda (z, lambda (v, U(o1)));

		trace_dem ("c = ", c);

                t = PIott (o1, a, Sotttxx (o, a, b, c1, c, y));
		return t;
	    }
            if (node(subdem(0,x)) == _ap &&
                node(subdem(0,subdem(0,x))) == _F)
            {
                /*
                if (typ (subdem(1,subdem(0,x))) == typ (subdem(1,x)))
                    return typ (subdem(1,x)); 
                error ("F applied to different types", __LINE__, x);
                */
                return unio (typ(subdem(1,subdem(0,x))), 
                             typ(subdem(1,x)));
            }        
	    f = fnc (x);
	    z = arg (x);
	    /* PIab = typ (f);
            b = arg (PIab); */
            tf = typ (f);
            tz = typ (z);
        new_tz:
            print_string (print_param, "typ(z) = ");
            print_dem (print_param, tz);
        new_tf:    
            print_string (print_param, "  subdem(1,subdem(0,tf)) = ");
            print_dem (print_param, subdem(1,subdem(0,tf)));
            print_string (print_param, "\n");

            if (node(tf) == _ap &&
                node(subdem(0,tf)) == _ap &&
                node(subdem(0,subdem(0,tf))) == _F &&
                inclus (tz, subdem(1,subdem(0,tf))))
                return subdem(1,tf);

            if (node(tf) == _ap &&
                node(subdem(0,tf)) == _ap &&
                node(subdem(0,subdem(0,tf))) == _PI &&
                inclus (tz, subdem(1,subdem(0,tf))))
                {
                    /* return ap (subdem(1,tf), z); */
                    tf1 = subdem(1,tf);
                    print_string (print_param, "tf1 = ");
                    print_dem (print_param, tf1);
                    print_string (print_param, "\nz = ");
                    print_dem (print_param, z);
                    r = ap (tf1, z);
                    print_string (print_param, "\nr = ");
                    print_dem (print_param, r);
                    print_string (print_param, "\n");
                    return r;
                }
            print_string (print_param, "Bad type of function ");
            print_dem (print_param, f);
            print_string (print_param, " of type ");
            print_dem (print_param, tf);
            print_string (print_param, " applied to ");
            print_dem (print_param, z);
            print_string (print_param, " of type ");
            print_dem (print_param, tz);
            print_string (print_param, "\n");

            tf1 = simplif (tf);
            if (tf1 != tf)
            {
                tf = tf1;
                goto new_tf;
            }

            tz1 = simplif (tz);
            if (tz1 != tz)
            {
                tz = tz1;
                goto new_tz;
            }

            print_string (print_param, "Bad type of function ");
            print_dem (print_param, f);
            print_string (print_param, " of type ");
            print_dem (print_param, tf);
            print_string (print_param, " applied to ");
            print_dem (print_param, z);
            print_string (print_param, " of type ");
            print_dem (print_param, tz);
            print_string (print_param, "\n");

            error ("Bad type of function : ", __LINE__, tf);


                
	    /*bz = ap (b, z);
	    return bz;*/

        case _Lambda:
            z = subdem(0,x);
            r = subdem(1,x);
            a = typ (z);
            bz = typ (r);
            b = lambda (z, bz);
            t = PItt (a, b);
            return t;
            break;

        default:
	    print_string (print_param, "typ not implemented for ");
	    print_dem (print_param, x);
	    print_string (print_param, "\n");
	    return U(-1);

    }
#endif
}

/* ap (typ_ap(ap(f,x)), x) = typ (ap(f,x)) */
DEM typ_ap (DEM r)
{
DEM a, b, c, u, v, w, bz, cz, PIbzcz, bz1, tf, tf1, r1;
ORDER o, o1;
    if (node(r) == _ap)
    {
        /*
	if (subdem(1,r) == z && !in (z, subdem(0,r)))
            return subdem(0,r);
        a = typ (z);
        u = typ (a);
	*/
        bz = typ (subdem(1,r));
        /* b = fnc (bz); */
        /* b = lambda (z, bz); */
        /*PIbzcz = typ (subdem(0,r));
          cz = arg (PIbzcz);*/
        tf = typ (subdem(0,r));
    new_tf:
        if (node(tf) == _ap &&
            node(subdem(0,tf)) == _ap)
        {
            if (node(subdem(0,subdem(0,tf))) == _F)
            {
                o = order(subdem(0,subdem(0,tf)));
                bz1 = subdem(1,subdem(0,tf)); 
                /* cz = Kottx (suc_order(o),*U(o)*/
		cz = Kttx (typ(subdem(1,tf)), bz1, subdem(1,tf));
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
        /* error ("Bad type of function in lambda", __LINE__, tf); */
	return NULL; 
	/* c = fnc (cz); */
        /*c = lambda (z, cz);*/
    re:
	return cz;
#if 0
        c = lambda (z, cz);
        o1 = max_order (order_u(u), max_order (order_u(typ(bz)), 
           order_u(typ(tf)) ));                                     

	return Sotttxx (pred_order (o1/*order_u (u)*/), a, b, c,
	    lambda (z, subdem(0,r)), 
	    lambda (z, subdem(1,r)));
#endif    
    }
    else
    {
        /* error ("typ_ap : bad ap :", __LINE__, r); */
	return NULL;
/*
	a = typ (z);
	b = typ (r);
	u = typ (a);
        return Kottx (pred_order (order_u(u)), b, a, r);
*/
    }

}

