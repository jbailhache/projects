
/* #include "config.h" */

#define CPP  

#ifdef CPP
#define far
#endif

#define TURBO_C 
/* #define VAX_C */ 

#ifndef VAX_C
/* #define ALLOC */
#endif

#include <stdio.h>
#include <errno.h>
#include <string.h>
#ifdef TURBO_C
#include <dos.h>
#endif

#ifndef TURBO_C
#define far 
#endif

#ifdef ALLOC
#define NULL MK_FP(0,0)
#endif

/* #define TRACE */

/* #define LAMBDA */

#define LAMBDA_DB 

#define FLAG_RED_LAMBDA 1

#define FLAG_PERM 0x1000

extern int flags;

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
 
typedef struct S_DEM
#ifdef ALLOC
                        far
#endif
                                *DEM;
 
enum dem_node {  _Var, _I, _It, _IT, _K, _Kt, _KT, _S, _St, _ST, _Yt, _YT,
    _E, _If, 
    _itransym, _idefI, _idefK, _idefS,
    _ileft, _iright, _ieq, _inode, _isubdem0, _isubdem1, _isubdem2,
    _ired, _iredu, _iext, _istep, _irstep,
    _nil, _cons, 
    _Sym, _Axm,
    _F, _PI, _U,
    _Ord, _Zero, _Suc, _Lim, _Rept, _Testt, 
    _ap, _transym, _defI, _defK, _defS,
    _Lambda, _DBLambda, _DBVar, _DB_Subst,
    _Subst, _Ext, _NoRed,
    _Ext1, _Ext2, _Ext3, _Ext4, _Ext5, _Ext6,
    _AE, _EA, _EA0, _EXT, _MP, _AI, _AK, _AS, _RPA,
    _ZeroIsOrd, _SucIsOrd, _LimIsOrd, _PredIsOrd, _StepIsOrd, _TfI,
    _IfNode, _Hyp
 };

extern int arity [];

typedef enum dem_node NODE;

struct S_DEM
{
    NODE _node;
    ORDER _order;
#ifdef NAME
#ifdef ALLOC
    char far *_name;
#else
    char *_name; 
#endif
#endif
    DEM _left, _right, _red[2];
    DEM _subdem [3];
#ifdef VAX_C
    char _buf[16];
#else
#ifdef ALLOC
    char _buf[10];
#else
    /* char _buf[4]; */
    char _buf[16];
#endif
#endif
};

#define node(x) ((x)->_node)
#define order(x) ((x)->_order)
#define level(x) ((x)->_order)

#ifdef NAME
#define name(x) ((x)->_name)
#else
#define name(x) ((x)->_buf)
#endif
#define subdem(i,x) ((x)->_subdem[i])

#ifdef TURBO_C
#define MAX_DEM 400
#else         /* V98 */

#ifdef VAX_C
#define MAX_DEM 30000
#else
#ifdef ALLOC
#define MAX_DEM 5000
#else
#ifdef CPP
#define MAX_DEM 6000
#else
#define MAX_DEM 1100
#endif
#endif
#endif

#endif

#ifdef ALLOC
extern struct S_DEM far *dems;
#else
extern struct S_DEM dems[MAX_DEM];
#endif
extern int n_dem;

DEM mk_dem (NODE node_, ORDER order_, char *name_, 
    DEM sd0, DEM sd1, DEM sd2, DEM sd3, DEM sd4, DEM sd5);

#define Var(name_,a) mk_dem (_Var, 0, name_, a, NULL, NULL, NULL, NULL, NULL)
#define DBVar(n) mk_dem (_DBVar, n, NULL, NULL, NULL, NULL, NULL, NULL, NULL)

#define Sym(name_) mk_dem (_Sym, 0, name_, \
    NULL, NULL, NULL, NULL, NULL, NULL)

#define Axm(a,b) mk_dem (_Axm, 0, NULL, a, b, NULL, NULL, NULL, NULL)

#define IT(o)    mk_dem (_IT,  o, NULL, NULL, NULL, NULL, NULL, NULL, NULL)
#define KT(o)    mk_dem (_KT,  o, NULL, NULL, NULL, NULL, NULL, NULL, NULL)
#define ST(o)    mk_dem (_ST,  o, NULL, NULL, NULL, NULL, NULL, NULL, NULL)
#define YT(o)    mk_dem (_YT,  o, NULL, NULL, NULL, NULL, NULL, NULL, NULL)
#define F(o)    mk_dem (_F, o, NULL, NULL, NULL, NULL, NULL, NULL, NULL)
#define PI(o)    mk_dem (_PI,  o, NULL, NULL, NULL, NULL, NULL, NULL, NULL)
#define U(o)    mk_dem (_U,  o, NULL, NULL, NULL, NULL, NULL, NULL, NULL)

#define ap1(f,a) mk_dem (_ap, 0, NULL, f, a, NULL, NULL, NULL, NULL)

#define It(o,a) mk_dem (_It, o, NULL, a, NULL, NULL, NULL, NULL, NULL)
#define Kt(o,a,b) mk_dem (_Kt, o, NULL, a, b, NULL, NULL, NULL, NULL)
#define St(o,a,b,c) mk_dem (_St, o, NULL, a, b, c, NULL, NULL, NULL)
#define Yt(o,a) mk_dem (_Yt, o, NULL, a, NULL, NULL, NULL, NULL, NULL)

/*
#define defI(o,a,x)	    mk_dem (_defI, o, NULL, a, x, \
    NULL, NULL, NULL, NULL)
#define defK(o,a,b,x,y)	    mk_dem (_defK, o, NULL, a, b, x, y, NULL, NULL)
#define defS(o,a,b,c,x,y,z) mk_dem (_defS, o, NULL, a, b, c, x, y, z)
*/

#define cons(x,y) mk_dem (_cons, Order(0), NULL, x, y, NULL, NULL, NULL, NULL)

#define defI(x)         mk_dem (_defI, Order(0), NULL, x, \
    NULL, NULL, NULL, NULL, NULL)
#define defK(x,y)     mk_dem (_defK, Order(0), NULL, x, y, NULL, NULL, NULL, NULL)
#define defS(x,y,z) mk_dem (_defS, Order(0), NULL, x, y, z, NULL, NULL, NULL)

#define EA(x)         mk_dem (_EA, Order(0), NULL, x, \
    NULL, NULL, NULL, NULL, NULL)

#define IfNode(p,q) mk_dem (_IfNode, Order(0), NULL, p, q, NULL, NULL, NULL, NULL)
#define Hyp(h,f) mk_dem (_Hyp, Order(0), NULL, h, f, NULL, NULL, NULL, NULL);

#define Rept(a) mk_dem (_Rept, 0, NULL, a,  NULL, NULL, NULL, NULL, NULL)
#define Testt(a) mk_dem (_Testt, 0, NULL,  a,  NULL, NULL, NULL, NULL, NULL)

#define Lambda(z,r) mk_dem (_Lambda, 0, NULL, z, r, NULL, NULL, NULL, NULL)
#define DBLambda(r) mk_dem (_DBLambda, 0, NULL, r, NULL, NULL, NULL, NULL, NULL)
#define DB_Subst(y,z) mk_dem (_DB_Subst, 0, NULL, y, z, NULL, NULL, NULL, NULL)

#define Subst(x,y,z) mk_dem (_Subst, 0, NULL, x, y, z, NULL, NULL, NULL)
#define Ext(x,y) mk_dem (_Ext, 0, NULL, x, y, NULL, NULL, NULL, NULL)

#define NoRed(x) mk_dem (_NoRed, 0, NULL, x, NULL, NULL, NULL, NULL, NULL)

#define app(f,a,b) ap (ap (f, a), b)
#define appp(f,a,b,c) ap (ap (ap (f, a), b), c)

#define RAP(rf,ra) ap (ap (rap, rf), ra)
#define RAPP(rf,ra,rb) RAP(RAP(rf,ra),rb)

#define LET(var,val,res) ap(lambda(var,res),val)

#if 1  
#ifdef VAX_C

#ifndef TRACE
#define trace_dem(s,d) trace_dem1 (__FILE__, __LINE__, s, d, "d", 0)
#else
#define trace_dem(s,d) trace_dem1 (__FILE__, __LINE__, s, d, "d", 1)
#endif                                                   
#else
#ifndef TRACE
#define trace_dem(s,d) trace_dem1 (__FILE__, __LINE__, s, d, #d, 0)
#else
#define trace_dem(s,d) trace_dem1 (__FILE__, __LINE__, s, d, #d, 1)
#endif
#define trace_dem_1(s,d) trace_dem1 (__FILE__, __LINE__, s, d, #d, 1)
#endif
#else
#define trace_dem(s,d) \
{ \
char format[1000]; \
        sprintf (format, "\n%s(%d) %s : %s = ", __FILE__, __LINE__, s, #d); \
        print_string (print_param, format); \
        print_dem (print_param, d); \
	print_string (print_param, " : "); \
	print_dem (print_param, left(d)); \
	print_string (print_param, " = "); \
	print_dem (print_param, right(d)); \
        gets (format); \
}
#endif

extern DEM I, K, S, E, If,
        itransym, idefI, idefK, idefS,
        ileft, iright, ieq, inode, isubdem0, isubdem1, isubdem2,
        ired, iredu, iext, istep, irstep,
        nil,
        Ord, Zero, Suc, Lim,
	Ext1, Ext2, Ext3, Ext4, Ext5, Ext6,
        AE, EA0, MP, AI, AK, AS, RPA,
        ZeroIsOrd, SucIsOrd, LimIsOrd, PredIsOrd, StepIsOrd, TfI, dSubst,
        dDB_Subst, 
        SEI, KI, IfI, SIfI, SKSIfIf, KKI, l_AS, KKKI, Fa, l_RPA,
	l_ZeroIsOrd, l_SucIsOrd, l_LimIsOrd, l_PredIsOrd, l_StepIsOrd,
	r_ZeroIsOrd, r_SucIsOrd, r_LimIsOrd, r_PredIsOrd, r_StepIsOrd,
	l_Ext1, l_Ext2, l_Ext3, l_Ext4, l_Ext5, l_Ext6,
	r_Ext1, r_Ext2, r_Ext3, r_Ext4, r_Ext5, r_Ext6,
         l_EA0, r_EA0,
        ZeroOrd, SucOrd, LimOrd, l_TfI, r_TfI;

extern DEM *watch;
#define WATCH(d) watch = &(d);

extern DEM no_red[];
extern int nnr;

init ();

/*
let fnc = function ap(f,a) -> f;;
let arg = function ap(f,a) -> a;;
*/

error (char *s, char *file, int line, DEM d);

DEM fnc1 (DEM d, char *file, int line);

DEM arg1 (DEM d, char *file, int line);

#define fnc(d) fnc1 (d, __FILE__, __LINE__)
#define arg(d) arg1 (d, __FILE__, __LINE__)

#ifdef LAMBDA_DB
#define extens dbextens /*lambda*/
#else
#define extens exten
#endif

/*
let order_u = function U o -> o;;
*/

#define order_u(d) (order(d))

char far *alloc (long n);

DEM right (DEM d);

DEM left (DEM d);

DEM transym (DEM ab, DEM cd);
DEM transym1 (DEM ab, DEM cd);

int depth (DEM x);

DEM rfnc (int n, DEM x);

struct print_param
{
    int (*print_string_param) (struct print_param *p, char *s);
#ifdef CPP
    FILE *f;
#endif
};

print_string (struct print_param *p, char *s);

print_strint (struct print_param *p, char *s, int i);

print_dem (struct print_param *p, DEM d);

DEM read_dem ();

struct print_param_file
{
    int (*print_string_param) (struct print_param *p, char *s);
    FILE *f;
};

extern struct
#ifdef CPP
                print_param
#else
                print_param_file
#endif
                        print_param[1];

print_string_file (struct print_param_file *p, char *s);

print_string_nul (struct print_param *p, char *s);

/* trace_dem (char *s, DEM x); */

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

DEM ap (DEM f, DEM a);

DEM Fott (int o, DEM a, DEM b);
 
DEM unio (DEM t1, DEM t2); 

int in (DEM x, DEM y);

DEM typ1 (DEM x);

DEM typ (DEM x);

DEM lambda1 (DEM z, DEM r); 

/* DEM lambda (DEM z, DEM r); */

DEM lambda0 (char *file, int line, DEM z, DEM r);

#ifdef LAMBDA_DB
#define lambda(z,r) DB_lambda (z, r)
#else
#define lambda(z,r) lambda0 (__FILE__, __LINE__, z, r)
#endif

DEM simplify (DEM x);

DEM simplif (DEM x);

DEM simplif1 (DEM x);

DEM simplif2 (DEM x);

int inclus (DEM t1, DEM t2);

/* error (char *s, int line, DEM d); */

DEM sym (DEM ab);

DEM trans (DEM ab, DEM bc);

DEM red (DEM x); 
DEM redu (DEM x);

DEM ext (DEM x, DEM t);
DEM exten (DEM x, DEM t);

DEM dbshift (int m, int n, DEM x);

void break_debug(void);
ORDER gen_order (DEM x);
trace_dem1 (char *file, int line, char *s, DEM d, char *nd, int flag);
push (char *fnc0, DEM arg0, DEM arg1, DEM arg2);
void pop();
DEM DB_lambda (DEM x, DEM y);
void init_refl();
void global ();
DEM dbextens (DEM x, DEM y);
DEM subst (DEM a, DEM v, DEM x);
DEM DBsubst (int n, DEM y, DEM z);
DEM rep (DEM);
/* DEM red (DEM, int); */
DEM reduc (DEM, int);
DEM step (DEM);
DEM rstep (DEM);
DEM list_ap (DEM, DEM);
DEM red1 (DEM, int);
int atoi (char *);
DEM redu1 (DEM x);
int depth_l (DEM);
trace_stack (struct print_param *p);
DEM Kttx (DEM, DEM, DEM);




