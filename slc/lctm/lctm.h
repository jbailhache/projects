
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

int pred_order (int o);

ORDER max_order (ORDER o1, ORDER o2);

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

extern int arity [];

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
extern struct S_DEM dems[MAX_DEM];
extern int n_dem;

DEM mk_dem (NODE node, ORDER order, char *name, 
    DEM sd0, DEM sd1, DEM sd2, DEM sd3, DEM sd4, DEM sd5); 

#define Var(name,a) mk_dem (_Var, 0, name, a, NULL, NULL, NULL, NULL, NULL) 

#define I(o)    mk_dem (_I,  o, NULL, NULL, NULL, NULL, NULL, NULL, NULL)
#define K(o)    mk_dem (_K,  o, NULL, NULL, NULL, NULL, NULL, NULL, NULL)
#define S(o)    mk_dem (_S,  o, NULL, NULL, NULL, NULL, NULL, NULL, NULL)
#define Y(o)    mk_dem (_Y,  o, NULL, NULL, NULL, NULL, NULL, NULL, NULL)
#define F(o)    mk_dem (_F, o, NULL, NULL, NULL, NULL, NULL, NULL, NULL)
#define PI(o)    mk_dem (_PI,  o, NULL, NULL, NULL, NULL, NULL, NULL, NULL)
#define U(o)    mk_dem (_U,  o, NULL, NULL, NULL, NULL, NULL, NULL, NULL)

#define ap1(f,a) mk_dem (_ap, 0, NULL, f, a, NULL, NULL, NULL, NULL)

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

extern DEM Ord, Zero, Suc, Lim;

init ();

/*
let fnc = function ap(f,a) -> f;;
let arg = function ap(f,a) -> a;;
*/

error (char *s, int line, DEM d);

DEM fnc1 (DEM d, int line);

DEM arg1 (DEM d, int line);

#define fnc(d) fnc1 (d, __LINE__)
#define arg(d) arg1 (d, __LINE__)

/*
let order_u = function U o -> o;;
*/

#define order_u(d) (order(d))

DEM right (DEM d);

DEM left (DEM d);

DEM transym (DEM ab, DEM cd);

int depth (DEM x);

DEM rfnc (int n, DEM x);

struct print_param
{
    int (*print_string_param) (struct print_param *p, char *s);
};

print_string (struct print_param *p, char *s);

print_strint (struct print_param *p, char *s, int i);

print_dem (struct print_param *p, DEM d);

struct print_param_file
{
    int (*print_string_param) (struct print_param *p, char *s);
    FILE *f;
};

extern struct print_param_file print_param[1];

print_string_file (struct print_param_file *p, char *s);

print_string_nul (struct print_param *p, char *s);

trace_dem (char *s, DEM x);

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

#define PIott1(o,a,b) ap1 (ap1 (PI(o), a), b) 
/*
#define Fott(o,a,b) PIott (o, a, Kottx (suc_order(o), U(o), a, b))


DEM PIott (int o, DEM a, DEM b)
{
    return ap (ap (PI(o), a), b);
}
*/

DEM Fott (int o, DEM a, DEM b);
 
DEM unio (DEM t1, DEM t2); 

int in (DEM x, DEM y);

DEM typ1 (DEM x);

DEM typ (DEM x);

DEM lambda1 (DEM z, DEM r); 

/* DEM lambda (DEM z, DEM r); */

DEM lambda0 (char *file, int line, DEM z, DEM r);

#define lambda(z,r) lambda0 (__FILE__, __LINE__, z, r)

DEM simplify (DEM x);

DEM simplif (DEM x);

DEM simplif1 (DEM x);

DEM simplif2 (DEM x);

int inclus (DEM t1, DEM t2);

error (char *s, int line, DEM d);


