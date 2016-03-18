
#include "lctm.h"

DEM ap (DEM f, DEM x)
{
DEM y, t;
    y = ap1 (f, x);
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

DEM Fott (ORDER o, DEM a, DEM b)
{
    o = max_order (gen_order(typ(a)), gen_order(typ(b)));
    return Fott1 (o, a, b);
}

DEM PIott (ORDER o, DEM a, DEM b)
{
    o = max_order (gen_order(a), gen_order(b));
    return PIott1 (o, a, b);
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
    error ("Union not implemented with ", __LINE__, t2);
}

