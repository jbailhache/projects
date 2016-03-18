
#include "lctm.h"

struct S_DEM dems[MAX_DEM];
int n_dem = 0;

DEM Ord, Zero, Suc, Lim;

int arity [] = { 1, 0, 0, 0, 0, 0,  0, 0,
    2,  2,       1,    2,    3 };

struct print_param_file print_param[1];

global ()
{
}

