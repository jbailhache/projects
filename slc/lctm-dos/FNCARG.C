
#include "lctm.h"

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
