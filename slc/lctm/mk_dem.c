
#include "lctm.h"

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

