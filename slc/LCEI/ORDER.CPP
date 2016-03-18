
#include "lctm.h"

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

ORDER gen_order1 (DEM x)
{
    if (node(x) != _ap && node(x) != _Lambda)
	return order(x);
    else
	return max_order (gen_order1(subdem(0,x)), gen_order1(subdem(1,x)));
/*
    if (node(x) == _U)
	return order(x);
    if (node(x) == _ap && 
        node(subdem(0,x)) == _ap &&
	node(subdem(0,subdem(0,x))) == _F)
        return max_order (gen_order
*/
}

ORDER gen_order (DEM x)
{
ORDER o;

    print_string (print_param, "call gen_order ");
    print_dem (print_param, x);
    print_string (print_param, "\n");

    o = gen_order1 (x);

    print_strint (print_param, "result %d gen_order ", o);
    print_dem (print_param, x);
    print_string (print_param, "\n");

    return o;
}


