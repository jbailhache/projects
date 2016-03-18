
#include "lctm.h"

DEM fnc1 (DEM d, char *file, int line)
{
    if (node(d) == _ap)
       return subdem(0,d);
    error ("fnc of not ap", file, line, d);
}

DEM arg1 (DEM d, char *file, int line)
{
    if (node(d) == _ap)
       return subdem(1,d);
    error ("arg of not ap", file, line, d);
}
