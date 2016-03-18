
#include "lctm.h"

/* break_debug () { } */

DEM ap (DEM f, DEM x)
{
DEM y, t;
/*
    print_string (print_param, "\nap f=");
    print_dem (print_param, f);
    print_string (print_param, "\n   x=");
    print_dem (print_param, x);
*/
    if (f == NULL || x == NULL || f == (DEM)1 || x == (DEM)1)
    {
        print_string (print_param, "\nError in ap : \n\tfnc = ");
	print_dem (print_param, f);
	print_string (print_param, "\n\targ = ");
	print_dem (print_param, x);
        break_debug ();
    }
    y = ap1 (f, x);
/*
    print_string (print_param, "\n   y=");
    print_dem (print_param, y);
    print_string (print_param, "\n");
*/
    /* t = typ (y); */
    return y;
}

DEM apt (DEM f, DEM x)
{
DEM y, t;
    y = ap1 (f, x);
    t = typ (y); 
    return y;
}

DEM Kttx (DEM a, DEM b, DEM x)
{
ORDER o;
DEM ta, tb;
DEM r;
    ta = typ (a);
    tb = typ (b);
    o = max_order (order(ta), order(tb));
    r = Kottx (o, a, b, x);
    return r;
}


DEM Fott1 (int o, DEM a, DEM b)
{
    /* return PIott (o, a, Kottx (suc_order(o), U(o), a, b)); */
    return ap1 (ap1 (F(o), a), b); 
}

DEM Ftt (DEM a, DEM b)
{
ORDER o;
    o = max_order (gen_order(typ(a)), gen_order(typ(b)));
    return Fott1 (suc_order(o), a, b);
}

DEM Fott (ORDER o, DEM a, DEM b)
{
    return Ftt (a, b);
}

DEM PItt (DEM a, DEM b)
{
ORDER o;
    o = max_order (gen_order(a), gen_order(b));
    return PIott1 (suc_order(o), a, b);
}

DEM PIott (ORDER o, DEM a, DEM b)
{
    return PItt (a, b);
}

DEM transym (DEM ab, DEM cd)
{
DEM a, c;
    a = left (ab);
    c = left (cd);
    if (a == c)
        return mk_dem (_transym, 0, NULL, ab, cd, NULL, NULL, NULL, NULL);
    else
        /* return IT(0); */
	return I;
}

DEM transym1 (DEM ab, DEM cd)
{
    if (ab == cd)
        return right (ab);
    if (left(ab) == right(ab)) /* && left(ab) == left(cd)) */
        return cd; 
    return transym (ab, cd);
}

int depth (DEM x)
{
int dp;
    for (dp=0; node(x)==_ap; dp++)
        x = subdem(0,x);
    return dp;               
}

int depth_l (DEM x)
{
int dp;
    for (dp=0; node(x)==_ap || node(x)==_Lambda; dp++)
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

#if 0
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
#else

int in1 (DEM x, DEM y, DEM vars)
{
    if (y == NULL)
	return 0;
    if (x == y && !in1 (x, vars, I /*NULL*/))
        return 1;
    if (node(y) == _Lambda)
    {
        return in1 (x, subdem(1,y), ap(vars,subdem(0,y)));
    }
    if (node(y) != _ap)
        return 0;
    if (in (x, subdem(0,y)))
        return 1;
    if (in (x, subdem(1,y)))
        return 1;
    return 0;
}

int in (DEM x, DEM y)
{
    in1 (x, y, I /*NULL*/);
}
#endif

int inclus1 (DEM t1, DEM t2)
{
    if (t1 == t2)
        return 1;
    if (node(t1) == _U && node(t2) == _U &&
        order(t1) <= order(t2))
        return 1;
    if (depth(t1) == 2 && node(subdem(0,subdem(0,t1))) == _F &&
        depth(t2) == 2 && node(subdem(0,subdem(0,t2))) == _F &&
	inclus (subdem(1,subdem(0,t2)), subdem(1,subdem(0,t1))) &&
	inclus (subdem(1,t1), subdem(1,t2)))
	return 1;
    return 0;
}

int inclus (DEM t1, DEM t2)
{
int r;
    print_string (print_param, "Inclusion of ");
    print_dem (print_param, t1);
    print_string (print_param, " in ");
    print_dem (print_param, t2);
    print_string (print_param, "\n");

    r = inclus1 (t1, t2);

    print_strint (print_param, "inclusion=%d of ", r);
    print_dem (print_param, t1);
    print_string (print_param, " in ");
    print_dem (print_param, t2);
    print_string (print_param, "\n");
    
    return r;
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
    /* error ("Union not implemented with ", __LINE__, t2); */
    print_string (print_param, "\nUnion not implemented with ");
    print_dem (print_param, t2);
    print_string (print_param, "\n");
    return t1;
}

/*
DEM subst (DEM x, DEM y, DEM z)
{
    if (y == x)
        return z;
    if (node(y) == _ap)
        return ap (subst (x, subdem(0,y), z),
                   subst (x, subdem(1,y), z));    
    if (node(y) == _Lambda && subdem(0,y)==x)
        return y;
    return y;
}
*/

#ifdef CPP
int atoi (char *s)
{
int x;
    sscanf (s, "%d", &x);
    return x;
}
#endif

