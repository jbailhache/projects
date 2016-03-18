
#include <stdio.h>

/*
 
type ORDER = Order of int;;

let suc_order = function Order (o) -> Order (o+1);;

let pred_order = function Order n -> 
    if n > 0 then Order (n-1) else Order n;;
*/

typedef int ORDER;

#define Order(o) o

#define suc_order(o) ((o)+1)

int pred_order (int o)
{
    if (o > 0)
       return o-1;
    return o;
}

ORDER max_order (ORDER o1, ORDER o2)
{
    if (o1 >= o2)
        return o1;
    else
        return o2;
}

/*
type DEM = Var of string * DEM
	 | I of ORDER  
         | K of ORDER 
         | S of ORDER
         | Y of ORDER
         | PI of ORDER
         | U of ORDER
         | ap of DEM * DEM
         | transym of DEM * DEM
         | defI of ORDER * DEM
         | defK of ORDER * DEM * DEM 
         | defS of ORDER * DEM * DEM * DEM;;

*/

typedef struct S_DEM *DEM;

enum dem_node {  _Var, _It, _I, _Kt, _K, _St, _S, _Yt, _Y, _F, _PI, _U, 
    _Ord, _Zero, _Suc, _Lim, _Rept, _Testt, 
    _ap, _transym, _defI, _defK, _defS };

int arity [] = { 1, 0, 0, 0, 0, 0,  0, 0,
    2,  2,       1,    2,    3 };

typedef enum dem_node NODE;

struct S_DEM
{
    NODE _node;
    ORDER _order;
    char *_name;
    DEM _subdem [6];
};

#define node(x) ((x)->_node)
#define order(x) ((x)->_order)
#define name(x) ((x)->_name)
#define subdem(i,x) ((x)->_subdem[i])

#define MAX_DEM 3000
struct S_DEM dems[MAX_DEM];
int n_dem = 0;

DEM mk_dem (NODE node, ORDER order, char *name, 
    DEM sd0, DEM sd1, DEM sd2, DEM sd3, DEM sd4, DEM sd5) 
{
int i, order1;
NODE node1;
    for (i=0; i<n_dem; i++)
    {
	if (dems[i]._node == node &&
            dems[i]._order == order &&
	    (dems[i]._name == name || !strcmp (dems[i]._name, name)) &&
            dems[i]._subdem[0] == sd0 &&
            dems[i]._subdem[1] == sd1 &&
            dems[i]._subdem[2] == sd2 &&
            dems[i]._subdem[3] == sd3 &&
            dems[i]._subdem[4] == sd4 &&
            dems[i]._subdem[5] == sd5)
                return dems+i;
	/*
	node1 = dems[i].node;
        order1 = dems[i].order;
        if (node1 == node &&
            order1 == order &&
	    !strcmp (dems[i].name, name) &&
            dems[i].subdem[0] == sd0 &&
            dems[i].subdem[1] == sd1 &&
            dems[i].subdem[2] == sd2 &&
            dems[i].subdem[3] == sd3 &&
            dems[i].subdem[4] == sd4 &&
            dems[i].subdem[5] == sd5)
                return dems+i;
	*/
    }
    if (n_dem >= MAX_DEM)
    {
        fprintf (stderr, "Insufficient memory\n");
        exit (0);
    }
    i = n_dem;
    dems[i]._node = node;
    dems[i]._order = order;
    dems[i]._name = name;
    dems[i]._subdem[0] = sd0;
    dems[i]._subdem[1] = sd1;
    dems[i]._subdem[2] = sd2;
    dems[i]._subdem[3] = sd3;
    dems[i]._subdem[4] = sd4;
    dems[i]._subdem[5] = sd5;
    n_dem++;
    return dems+i;
}


#define Var(name,a) mk_dem (_Var, 0, name, a, NULL, NULL, NULL, NULL, NULL) 

#define I(o)    mk_dem (_I,  o, NULL, NULL, NULL, NULL, NULL, NULL, NULL)
#define K(o)    mk_dem (_K,  o, NULL, NULL, NULL, NULL, NULL, NULL, NULL)
#define S(o)    mk_dem (_S,  o, NULL, NULL, NULL, NULL, NULL, NULL, NULL)
#define Y(o)    mk_dem (_Y,  o, NULL, NULL, NULL, NULL, NULL, NULL, NULL)
#define F(o)    mk_dem (_F, o, NULL, NULL, NULL, NULL, NULL, NULL, NULL)
#define PI(o)    mk_dem (_PI,  o, NULL, NULL, NULL, NULL, NULL, NULL, NULL)
#define U(o)    mk_dem (_U,  o, NULL, NULL, NULL, NULL, NULL, NULL, NULL)

#define ap(f,a) mk_dem (_ap, 0, NULL, f, a, NULL, NULL, NULL, NULL)

#define It(o,a) mk_dem (_It, o, NULL, a, NULL, NULL, NULL, NULL, NULL)
#define Kt(o,a,b) mk_dem (_Kt, o, NULL, a, b, NULL, NULL, NULL, NULL)
#define St(o,a,b,c) mk_dem (_St, o, NULL, a, b, c, NULL, NULL, NULL)
#define Yt(o,a) mk_dem (_Yt, o, NULL, a, NULL, NULL, NULL, NULL, NULL)

#define defI(o,a,x)	    mk_dem (_defI, o, NULL, a, x, \
    NULL, NULL, NULL, NULL)
#define defK(o,a,b,x,y)	    mk_dem (_defK, o, NULL, a, b, x, y, NULL, NULL)
#define defS(o,a,b,c,x,y,z) mk_dem (_defS, o, NULL, a, b, c, x, y, z)

#define Rept(a) mk_dem (_Rept, 0, NULL, a,  NULL, NULL, NULL, NULL, NULL)
#define Testt(a) mk_dem (_Testt, 0, NULL,  a,  NULL, NULL, NULL, NULL, NULL)

DEM Ord, Zero, Suc, Lim;

init ()
{
    Ord = mk_dem (_Ord, 0, NULL, NULL,  NULL, NULL, NULL, NULL, NULL);
    Zero = mk_dem (_Zero, 0, NULL, NULL,  NULL, NULL, NULL, NULL, NULL);
    Suc = mk_dem (_Suc, 0, NULL, NULL,  NULL, NULL, NULL, NULL, NULL);
    Lim = mk_dem (_Lim,  0, NULL, NULL,  NULL, NULL, NULL, NULL, NULL);
}

/*
let fnc = function ap(f,a) -> f;;
let arg = function ap(f,a) -> a;;
*/

error (char *s, int line, DEM d);

DEM fnc1 (DEM d, int line)
{
    if (node(d) == _ap)
       return subdem(0,d);
    error ("fnc of not ap", line, d);
}

DEM arg1 (DEM d, int line)
{
    if (node(d) == _ap)
       return subdem(1,d);
    error ("arg of not ap", line, d);
}

#define fnc(d) fnc1 (d, __LINE__)
#define arg(d) arg1 (d, __LINE__)

/*
let order_u = function U o -> o;;
*/

#define order_u(d) (order(d))

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

DEM right (DEM d);

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


DEM transym (DEM ab, DEM cd)
{
DEM a, c;
    a = left (ab);
    c = left (cd);
    if (a == c)
        return mk_dem (_transym, 0, NULL, ab, cd, NULL, NULL, NULL, NULL);
    else
        return I(0);
}

int depth (DEM x)
{
int dp;
    for (dp=0; node(x)==_ap; dp++)
        x = subdem(0,x);
    return dp;               
}

DEM rfnc (int n, DEM x)
{
int i;
    for (i=0; i<n; i++)
        x = subdem(0,x);
    return x;
}

struct print_param
{
    int (*print_string_param) (struct print_param *p, char *s);
};

print_string (struct print_param *p, char *s)
{
    /* printf ("ps<%s>.\n", s); */
    (*(p->print_string_param)) (p, s);
}

print_strint (struct param *p, char *s, int i)
{
char buf[60];
    sprintf (buf, s, i);
    print_string (p, buf);
}

print_dem (struct print_param *p, DEM d)
{
int i, dp;
    switch (node(d))
    {
	case _Var :
	    print_string (p, name(d));
            print_string (p,":");
            print_dem (p, subdem(0,d));
	    break;

        case _I: print_strint (p, "I%d", order(d)); break;
        case _K: print_strint (p, "K%d", order(d)); break;
        case _S: print_strint (p, "S%d", order(d)); break;
        case _Y: print_strint (p, "Y%d", order(d)); break;
        case _F: print_strint (p, "F%d", order(d)); break;
        case _PI: print_strint (p, "PI%d", order(d)); break;
        case _U: print_strint (p, "U%d", order(d)); break;

	case _It:
	    print_strint (p, "It%d [", order(d));
	    print_dem (p, subdem(0,d));
	    print_string (p, "]");
            break;

	case _Kt:
	    print_strint (p, "Kt%d [", order(d));
            print_dem (p, subdem(0,d));
	    print_string (p, ", ");
	    print_dem (p, subdem(1,d));
	    print_string (p, "]");
            break;

	case _St:
	    print_strint (p, "St%d [", order(d));
	    print_dem (p, subdem(0,d));
            print_string (p, ", ");
            print_dem (p, subdem(1,d));
	    print_string (p, ", ");
	    print_dem (p, subdem(2,d));
            print_string (p, "]");
            break;

	case _Yt:
	    print_strint (p, "Yt%d [", order(d));
	    print_dem (p, subdem(0,d));
	    print_string (p, "]");
            break;

	case _Ord:
	    print_string (p, "Ord");
	    break;

	case _Zero:
	    print_string (p, "Zero");
	    break;

	case _Suc:
	    print_string (p, "Suc");
	    break;

	case _Lim:
	    print_string (p, "Lim");
	    break;

	case _Rept:
	    print_string (p, "Rept [");
	    print_dem (p, subdem(0,d));
	    print_string (p, "]");
            break;

	case _Testt:
	    print_string (p, "Testt [");
	    print_dem (p, subdem(0,d));
	    print_string (p, "]");
            break;


        /*case _ap: print_string (p, "(");*/
        psd01:    print_dem (p, subdem(0,d));
                  print_string (p, " ");
                  print_dem (p, subdem(1,d));
                  print_string (p, ")");
                  break;

        case _ap:
             print_string (p, "(");
             dp = depth (d);
             print_dem (p, rfnc(dp,d));
             for (i=dp-1; i>=0; i--)
             {
                 print_string (p, " ");
                 print_dem (p, subdem(1,rfnc(i,d))); 
             }    
             print_string (p, ")");
             break;

	case _transym:
	    print_string (p, "(transym ");
	    goto psd01;

        case _defI:
	    print_string (p, "(defI ");
	    goto psd01;

        case _defK:
	    print_string (p, "(defK ");
            print_dem (p, subdem(0,d));
	    for (i=1; i<=3; i++)
	    {
		print_string (p, " ");
		print_dem (p, subdem(i,d));
            }
            print_string (p, ")");
	    break;
    
        case _defS:
	    print_string (p, "(defS ");
            print_dem (p, subdem(0,d));
	    for (i=1; i<=5; i++)
	    {
		print_string (p, " ");
		print_dem (p, subdem(i,d));
            }
            print_string (p, ")");
	    break;    

        default: print_strint (p, "?%d", (int)(node(d))); 
        
        
             
             
    }

}

struct print_param_file
{
    int (*print_string_param) (struct print_param *p, char *s);
    FILE *f;
};

struct print_param_file print_param[1];

print_string_file (struct print_param_file *p, char *s)
{
    /* printf ("psf<%s>\n", s); */
    fprintf (p->f, "%s", s);
}

trace_dem (char *s, DEM x)
{
    print_string (print_param, s);
    print_dem (print_param, x); 
    print_string (print_param, "\n");		
}

/*
let Iot o a = ap (I o, a);;

let Kottx o a b x = ap (ap (ap (K o, a), b), x);;

let Sotttxx o a b c x y = ap (ap (ap (ap (ap (S o, a), b), c), x), y);;

let PIott o a b = ap (ap (PI o, a), b);;

let Fott o a b = PIott o a (Kottx (suc_order o) (U o) a b);; 

*/

#ifdef GEN_CB_T

#define Iot(o,a) ap (I(o), a)
#define Kottx(o,a,b,x) ap (ap (ap (K(o), a), b), x)
#define Sotttxx(o,a,b,c,x,y) ap (ap (ap (ap (ap (S(o), a), b), c), x), y)

#else

#define Iot(o,a) It(o,a)
#define Kottx(o,a,b,x) ap (Kt(o,a,b), x)
#define Sotttxx(o,a,b,c,x,y) ap (ap (St(o,a,b,c), x), y)

#endif

#define PIott(o,a,b) ap (ap (PI(o), a), b) 
/*
#define Fott(o,a,b) PIott (o, a, Kottx (suc_order(o), U(o), a, b))


DEM PIott (int o, DEM a, DEM b)
{
    return ap (ap (PI(o), a), b);
}
*/

DEM Fott (int o, DEM a, DEM b)
{
    /* return PIott (o, a, Kottx (suc_order(o), U(o), a, b)); */
    return ap (ap (F(o), a), b); 
}
 
DEM unio (DEM t1, DEM t2); 

int in (DEM x, DEM y)
{
    if (x == y)
	   return 1;
    if (node(y) != _ap)
        return 0;
    if (in (x, subdem(0,y)))
        return 1;
    if (in (x, subdem(1,y)))
        return 1;
    return 0;
}

DEM typ1 (DEM x);

DEM typ (DEM x)
{
DEM t;
    print_string (print_param, "Type of ");
    print_dem (print_param, x);
    print_string (print_param, "\n");
    
    t = typ1 (x);

    print_string (print_param, "type of ");
    print_dem (print_param, x);
    print_string (print_param, " is ");
    print_dem (print_param, t);
    print_string (print_param, "\n");

    return t;
}

DEM lambda1 (DEM z, DEM r); 

DEM lambda (DEM z, DEM r)
{
DEM l;
    print_string (print_param, "lambda ");
    print_dem (print_param, z);
    print_string (print_param, " ");
    print_dem (print_param, r);
    print_string (print_param, "\n");

    l = lambda1 (z, r);

    print_string (print_param, "lambda ");
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

    print_string (print_param, "simplif ");
    print_dem (print_param, x);
    print_string (print_param, "\n");

    y = simplify (x);

    print_string (print_param, "simplif ");
    print_dem (print_param, x); 
    print_string (print_param, " = ");
    print_dem (print_param, y);
    print_string (print_param, "\n");

    return y;
}

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
DEM a, b, c, u, v, w, bz, cz, PIbzcz, bz1, tf, tf1, r1;
ORDER o;
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
    re:
        c = lambda (z, cz);
	return Sotttxx (pred_order (order_u (u)), a, b, c,
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

}

/*
and typ = function
      Var (n, t) -> t
    | I o -> PIott (suc_order o) (U o)
		(lambda (Var ("a", U o))
	     	    (Fott (suc_order o) (Var ("a", U o)) (Var ("a", U o))) )
    | U o -> U (suc_order o)

    ;;		
*/

/*
int expr_typ (DEM x, DEM t)
{
DEM tx;
    tx = typ (x);
    if (typ(x) == t)
        return 1;
    
}
*/

int inclus (DEM t1, DEM t2)
{
    if (t1 == t2)
        return 1;
    if (node(t1) == _U && node(t2) == _U &&
        order(t1) <= order(t2))
        return 1;
    return 0;
}

DEM unio (DEM t1, DEM t2)
{
    if (node(t1) == _U && node(t2) == _U)
    {
        if (order(t1) >= order(t2))
            return t1;
        else
            return t2;
    }
    print_dem (print_param, t1);
    print_string (print_param, " ");
    error ("Union not implemented with ", __LINE__, t2);
}

DEM typ1 (DEM x)
{
int o, o1, o2;
DEM a, b, c, c1, f, x1, y, z, v, PIab, bz, s, tf, tf1, tz, tz1, t, n;

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

	case _I :
	    a = Var ("a", U(o1)); 
	    return PIott (o2, U(o1), lambda (a,
			   Fott (/*suc_order*/(o1), a, a) ));

	case _Kt:
	    a = subdem(0,x);
	    b = subdem(1,x);
	    t =  Fott (o1, a, Fott (o1, b, a));
	    return t;

	case _K :
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

	case _S :
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
	    t = Fott (o1, Ord, Fott (o1, ap (a, Zero), 
		    PIott (o1, Ord, lambda (n, ap (a, ap (Suc, n)))) ));
	    return t;

        case _F:
            return Fott (o1, U(o), Fott (o1, U(o), U(o)));

	case _PI:
	    a = Var ("a", U(o));
	    return PIott (o1, U(o), lambda (a,
			    Fott (o1, Fott (o1, a, U(o)), U(o)) ));
		     
        case _U: return U (suc_order (order_u (x)));

	case _ap:
	    if (depth(x) == 1 && node(s=rfnc(1,x)) == _K)
	    {
		a = subdem(0,s);
		b = subdem(1,s);
		o = order(s);
		return Fott (o, b, a);
            }
	    if (node(subdem(0,x)) == _ap &&
	        node(subdem(0,subdem(0,x))) == _ap &&
		node(subdem(0,subdem(0,subdem(0,x)))) == _K)
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
	    if (depth (x) == 5 && node(s=rfnc(5,x)) == _S)
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
                inclus (typ(z), subdem(1,subdem(0,tf))))
                return subdem(1,tf);

            if (node(tf) == _ap &&
                node(subdem(0,tf)) == _ap &&
                node(subdem(0,subdem(0,tf))) == _PI &&
                inclus (typ(z), subdem(1,subdem(0,tf))))
                return ap (subdem(1,tf), z);

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

            error ("Bad type of function : ", __LINE__, tf);


                
	    /*bz = ap (b, z);
	    return bz;*/


        default:
	    print_string (print_param, "typ not implemented for ");
	    print_dem (print_param, x);
	    print_string (print_param, "\n");
	    return U(-1);

    }
}

error (char *s, int line, DEM d)
{
    fprintf (stderr, "Error at line %d : %s ", line, s);
    print_dem (print_param, d);
    exit (1);
}

main ()
{
DEM d, ford, tford, f, n, p, nrtxf;
    print_param->print_string_param = print_string_file;
    print_param->f = stdout;
    print_string (print_param, "Bonjour\n");

    init ();

    d = left (mk_dem (_defI, 3, NULL, U(5), K(2), NULL, NULL, NULL, NULL));
    print_dem (print_param, d);

    d = typ (I(30));
    print_dem (print_param, d);    
/*
    d = typ (K(40));
    print_dem (print_param, d);
*/
        
    f = Var ("f", Fott (Order(2), Ord, U(Order(1))));
    n = Var ("n", Ord);
    p = Var ("p", Ord);
    nrtxf = Var ("nrtxf", Ord);
        /*
        ford = ap (Y(fnc(ORD,TYPE)), lambda (f, lambda (n,
                ap (ap (ap (ap (TEST, ap (K(TYPE,ORD), TYPE)), n), T_ORD),
                        lambda (p, ap (ap (T_FNC, ap (f, p)), ap (f, p)))
                        ) )));
        */

    ford = ap (Yt(Order(1),Fott(Order(2),Ord,U(Order(1)))), lambda (f, 
	    lambda (n,
	     ap (ap (ap (Testt(Kottx(Order(1),U(Order(1)),Ord,U(Order(1)))),
		n), Ord), 
		    lambda (p, Fott (Order(1), ap (f, p), ap (f, p))) ) ) ));
      
    tford = typ (ford);

    print_string (print_param, "ford = ");
    print_dem (print_param, ford);
    print_string (print_param, "\ntford = ");
    print_dem (print_param, tford);
    print_string (print_param, "\n");
    
}


