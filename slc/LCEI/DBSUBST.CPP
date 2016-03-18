
#include "lctm.h"

DEM DBsubst (int n, DEM y, DEM z)
{
    if (y == NULL)
        return NULL;
    if (node(y) == _DBVar)
    {
        if (level(y) == n)
        	return z;
	if (level(y) > n)
		return DBVar (level(y)-1);
    }
    if (node(y) == _ap)
        return ap (DBsubst (n, subdem(0,y), z),
                   DBsubst (n, subdem(1,y), z));
    if (node(y) == _DBLambda)
        return DBLambda (DBsubst (n+1, subdem(0,y), dbshift (0, 1, z)));
    /* return y; */
    return mk_dem (node(y), order(y), name(y),
    			DBsubst (n, subdem(0,y), z),
    			DBsubst (n, subdem(1,y), z),
    			DBsubst (n, subdem(2,y), z),
                        NULL, NULL, NULL /*,
    			DBsubst (n, subdem(3,y), z),
    			DBsubst (n, subdem(4,y), z),
    			DBsubst (n, subdem(5,y), z)*/);
}

DEM DBname (int n, DEM x, DEM y)
{
    if (y == NULL)
        return NULL;
    if (x == y)
        return DBVar(n);
    if (node(y) == _ap)
        return ap (DBname (n, x, subdem(0,y)),
                   DBname (n, x, subdem(1,y)));
    if (node(y) == _DBLambda)
        return DBLambda (DBname (n+1, x, subdem(0,y)));
    /* return y; */
    return mk_dem (node(y), order(y), name(y),
	DBname (n, x, subdem(0,y)),
        DBname (n, x, subdem(1,y)),
	DBname (n, x, subdem(2,y)),
        NULL, NULL, NULL /*,
	DBname (n, x, subdem(3,y)),
	DBname (n, x, subdem(4,y)),
	DBname (n, x, subdem(5,y))*/);
}

DEM DB_lambda (DEM x, DEM y)
{
    return DBLambda (DBname (0, x, y));
}

DEM dbextens (DEM x, DEM y)
{
    if (node(y) == _ap && subdem(1,y) == x && !in (x, subdem(0,y)))
        return subdem(0,y);
    return lambda (x, y);
}

DEM dbshift (int m, int n, DEM x)
{
    if (x == NULL)
        return NULL;
    if (node(x) == _DBVar)
        if (level(x) >= m)
            return DBVar (level(x)+n);
        else
            return x;
    if (node(x) == _DBLambda)
        return DBLambda (dbshift (m+1, n, subdem(0,x)));
    if (node(x) == _Var || node(x) == _Sym)
        return mk_dem (node(x), order(x), name(x), 
               NULL, NULL, NULL, NULL, NULL, NULL);
    return mk_dem (node(x), order(x), NULL,
           dbshift (m, n, subdem(0,x)), 
           dbshift (m, n, subdem(1,x)), 
           dbshift (m, n, subdem(2,x)),
           NULL, NULL, NULL);
}
