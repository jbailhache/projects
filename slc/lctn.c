/* [JACQUES.D1]LCT.C */

/* #define TRACE */
/* #define TRACE_TYPE */
/* #define TRACE1 */
/* #define TRACE_TERM */

#include <stdio.h>
#include <errno.h>
#include <stdlib.h>

#include "stream.h"

/*
struct param_file param_out = { stdout },
		  param_err = { stderr },
		  param_trc = { stderr };
*/
struct param_file param_out, param_err, param_trc;

struct put_fnct out[1] = { f_put_file, &param_out },
		err[1] = { f_put_file, &param_err },
		trc[1] = { f_put_file, &param_trc };

#define TYPE_ORD 'O'
#define TYPE_UNDEF 'U'
#define TYPE_FNC 'F'

#define TYPE_TYPE 'T'
#define TYPE_PFNC 'f'
#define TYPE_TRM 't'

union u_term;

union u_type
{
	char k;
	struct type_fnc
	{
		char k;
		union u_type *arg;
		union u_type *res;
	} fnc;
	struct type_pfnc /* f : a->>b, x : a => fx : bx */
	{
		char k;
		union u_type *arg;
		union u_term *res; /* fonction qui a(u type de) l'argument
					associe le type du resultat */
	} pfnc;
	struct type_trm
	{
		char k;
		union u_term *typ;
	} trm;
};

typedef union u_type *type;

union u_type ORD[1], UNDEF[1], TYPE[1];

#define TERM_I 'I'
#define TERM_K 'K'
#define TERM_S 'S'
#define TERM_Y 'Y'
#define TERM_ZERO '0'
#define TERM_SUC '\''
#define TERM_LIM 'L'
#define TERM_REP 'R'
#define TERM_AP '-'
#define TERM_VAR 'V'
#define TERM_UNDEF 'U'

#define TERM_It 'i' /* It t = I[t] */
#define TERM_Kt 'k'
#define TERM_St 's'
#define TERM_Yt 'y'

#define TERM_TEST '?'
/* test a n:O z:an s:an
	test: T ->> \a. O ->> \n. an -> (O -> an) -> an */
#define TERM_REPt 'r'

#define TERM_ABST '\\'

union u_term
{
	char k;
	struct
	{
		char k;
		type typ;
	} term;
	struct term_I
	{
		char k;
		type typ;
		type a;
	} I;
	struct term_K
	{
		char k;
		type typ;
		type a, b;
	} K;
	struct term_S
	{
		char k;
		type typ;
		type a, b, c;
	} S;
	struct term_Y
	{
		char k;
		type typ;
		type a;
	} Y;
	struct term_rep
	{
		char k;
		type typ;
		type a;
	} rep;
	struct term_ap
	{
		char k;
		type typ;
		union u_term *fnc, *arg;
	} ap;
	struct term_var
	{
		char k;
		type t;
		char *name;
		type typ;
	} var;
	struct term_abst
	{
		char k;
		type t;
		union u_term *arg, *res;
	} abst;
};

typedef union u_term *term;

union u_term ZERO[1], SUC[1], LIM[1], UNDEF_TERM[1],
	It[1], Kt[1], St[1], Yt[1], TEST[1], REPt[1];

union u_term T_ORD[1], T_UNDEF[1], T_TYPE[1], T_FNC[1], T_PFNC[1];

#define MAX_PREMISSES 3

/* union u_dem */

struct s_dem
{
	char k;
	term left, right;
	char *name;
	int n_premisses;
	struct s_dem *premisse[MAX_PREMISSES];
	/*
	struct dem_axiom
	{
		char k;
		term mg, md;
		char *name;
	}
	struct dem_sym
	{
		char k;
		term mg, md;
		union u_dem *
	*/
};

#define DEM_AXIOM '!'
#define DEM_SYM 'x'	/* a=b => b=a */
#define DEM_TRANS 't'	/* a=b, b=c => a=c */
#define DEM_AP 'A'	/* f:A->B=g:A->B, a:A=b:A => fa:B=gb:B */
#define DEM_APt 'a'     /* A:T=A' f:A->B=g a:A'=b => fa=gb */
#define DEM_I 'I'	/* a:A=b:A => I[A]a:A=b:A */
#define DEM_K 'K'	/* a:A=a', b:B=b' => K[A,B]ab = a' */
#define DEM_S 'S'	/* a:A->B->C=a', b:A->B=b', c:A=c' =>
				S[A,B,C]abc = a'c'(b'c') */
#define DEM_Y 'Y'	/* f:A->A=g => Y[A]f = f(Y[A]f) */
#define DEM_It 'i'	/* a:A=a' => iAa=a' */
#define DEM_Kt 'k'	/* a:A=a', b:Ba=b' => kABab = a' */
#define DEM_Ktt 'l'
#define DEM_St 's'	/* a:A->>\x(BX->>CX)=a', b:A->>B, c:A =>
				sABCabc = a'c'(b'c') */
#define DEM_Yt 'y'	/* f:A->A=f' => yAf = f(yAf) */
#define DEM_REP0 'Z'    /* f:A->A=f', x:A=x' => R[A]0fx=x' */
#define DEM_REPEX '['	/* f:A->A=f' x:A=x' n:O=n' =>
				R[A](suc n)fx = f(R[A]nfx) */
#define DEM_REPIN ']'	/*			(ou R[A]nf(fx) ?) */
#define DEM_REPt0 'z'	/* f:A->A=f' x:A=x' => rAofx = x' */
#define DEM_REPtEX '>'	/* f:A->A=f' x:A=x' n:O=n' =>
				rA(suc c)fx = f(rAnfx) */
#define DEM_REPtIN '<'	/*			(ou rAnf(fx) ? */
#define DEM_TEST0 '0'	/* z:A0=z' s:O->>\n:A(n+1) => ?Azs = 0 */
#define DEM_TEST1 '1'   /* z:A0=z' s:O->>\n:A(n+1) n:O=n' =>
				?(suc n)zs = sn */
#define DEM_ABST '\\'
#define DEM_SUBST '/' /* x:A=x' y:B=y' z:A=z' => (\x.y)z = subst(x',y',z') */

#define DEM_EQTYPE 'T'

typedef struct s_dem *dem;

struct s_dem EX_ZERO[1], EX_SUC[1], EX_LIM[1], EX_UNDEF_TERM[1],
	EX_It[1], EX_Kt[1], EX_St[1], EX_Yt[1], EX_TEST[1], EX_REPt[1],
	EX_ORD[1], EX_UNDEF[1], EX_TYPE[1], EX_FNC[1], EX_PFNC[1];

type TYPE_It, TYPE_Kt, TYPE_St, TYPE_TFNC, TYPE_TPFNC, TYPE_REPt, TYPE_TEST;

int flag_control = 1;

#define ALLOC(x,t) \
{ \
	(x) = malloc (sizeof (t)); \
	if ((x) == NULL) \
	{ \
	char buf[200]; \
		sprintf (buf, \
			"%s(%d): insufficient memory to allocate %s %s\n", \
			__FILE__, __LINE__, #t, #x); \
		sput (buf, err); \
		exit (-1); \
	} \
}

#define FREE free

type _t;

#ifdef TRACE_TERM
#define trace_term(_x) \
{ \
char buftrace[50]; \
	sprintf (buftrace, "%s(%d) [%X,%X]: ", \
		__FILE__, __LINE__, 0, 0); \
	_t = type_term (_x);                    \
	sput ("\nType of " #_x " = ", out); \
	write_term (_x, out);                \
	sput (" is ", out);                  \
	write_type (_t, out);                \
}

#else
#define trace_term(_x)
#endif

int equal_type (type a, type b);
int equal_term (term x, term y);

term ap (term fnc, term arg);
term lambda (term v, term x);

term term_from_type (type t);
type type_from_term (term x);

write_type (type t, struct put_fnct *put);
write_term (term t, struct put_fnct *put);

type fnc (type a, type b);
type pfnc (type a, term b);

term var (char *name, type t);

term plambda (term v, /*type t,*/ term x);

term canonic_term (term x);

type type_term (term x);
type calcul_type_term (term x);

term abst (term arg, term res);

term lambdax (term v, term x);
term plambdax (term v, term x);

init ()
{
term t, a, b, c, x1, n, f, g;
type r, t1;
term tmp[40];
	t = var ("t", TYPE);
	a = var ("a", TYPE);
	b = var ("b", TYPE);
	c = var ("c", TYPE);
	x1 = var ("x1", TYPE);
	n = var ("n", ORD);

/*
	out->f = f_put_file;
	out->p = param_out;

	err->f = f_put_file;
	err->p = param_err;
*/
	ORD->k = TYPE_ORD;
	UNDEF->k = TYPE_UNDEF;
	TYPE->k = TYPE_TYPE;

	ZERO->k = TERM_ZERO; ZERO->term.typ = ORD;
	SUC->k = TERM_SUC; SUC->term.typ = fnc (ORD, ORD);
	LIM->k = TERM_LIM; LIM->term.typ = calcul_type_term (LIM);
	trace_term (LIM);
	UNDEF_TERM->k = TERM_UNDEF; UNDEF_TERM->term.typ = UNDEF;

	T_ORD->k = TYPE_ORD; T_ORD->term.typ = TYPE;
	T_UNDEF->k = TYPE_UNDEF; T_UNDEF->term.typ = TYPE;
	T_TYPE->k = TYPE_TYPE; T_TYPE->term.typ = TYPE;
	T_FNC->k = TYPE_FNC; T_FNC->term.typ = fnc (TYPE, fnc (TYPE, TYPE));
	T_PFNC->k = TYPE_PFNC; T_PFNC->term.typ = calcul_type_term (T_PFNC);
	trace_term (T_PFNC);

	It->k = TERM_It;
	Kt->k = TERM_Kt;
	St->k = TERM_St;
	Yt->k = TERM_Yt;
	TEST->k = TERM_TEST;
	REPt->k = TERM_REPt;

	/*TYPE_TFNC = fnc (TYPE, fnc (TYPE, TYPE));*/

	TYPE_TPFNC = pfnc (TYPE, lambda (t,
				ap (ap (T_FNC,
					ap (ap (T_FNC, t), T_TYPE)
					), T_TYPE)
					  ));
	T_PFNC->term.typ = TYPE_TPFNC;
	trace_term (T_PFNC);

	TYPE_It = pfnc (TYPE, lambda (t, ap (ap (T_FNC, t), t)));
	It->term.typ = TYPE_It;
	trace_term (It);

	FREE (b); b = var ("b", /*fnc (a, TYPE)*/
			/*type_from_term (canonic_term (ap (a, T_TYPE)))*/
			type_from_term (ap (ap (T_FNC, a), T_TYPE)) );
	FREE (x1); x1 = var ("x1", type_from_term (a));
	FREE (c); c = var ("c", type_from_term (ap (ap (T_FNC, a),
		ap (ap (T_FNC, ap (b, x1)), T_TYPE) )));
	/* g = var ("g", type_from_term (ap (ap (T_PFNC, a), b))); */
	/* t = ap (ap (T_PFNC, a), b); */
	trace_term (T_PFNC);
	trace_term (a);
	tmp[1] = ap (T_PFNC, a); trace_term (tmp[1]);
	tmp[2] = ap (tmp[1], b);
	t1 = type_from_term (tmp[2]);
#ifdef TRACE
	sput ("\nt1 = ", err);
	write_type (t1, err);
#endif
	g = var ("g", t1);

		/* a:T -> b:a->T -> c:a->(bx)->T  	S'[a,b,c]:
			f:(a->>\x.(bx->>cx)) ->
			g:(a->>b) ->
			x:a -> cx(gx)
		St: T->>\a. (a->T)->>\b. (a->(bx)->T)->>\c.
			(a->>\x.(bx->>cx)) -> ((a->>b)->>\g.
				a->>\x.(cx(gx)))

			(a->>\x.(bx->>cx)) -> (a->>b) -> a ->>\x.cx(bx) */
	/*
	TYPE_St = pfnc (TYPE, lambda (a,
		ap (ap (T_PFNC, ap(a,T_TYPE)), plambda (b,
		    ap (ap (T_PFNC,
			ap (ap (T_FNC, a), ap (ap (T_FNC, ap (b, x1)), T_TYPE))),
			plambda (c,
			    ap (ap (T_FNC,
				ap (ap (T_PFNC, a), lambda (x1,
					ap (ap (T_PFNC, ap (b, x1)), ap (c, x1))
						))),
				ap (ap (T_PFNC,
				    ap (ap (T_PFNC, a), b) ),
				    lambda (g,
					ap (ap (T_PFNC, a), lambda (x1,
						ap (ap (c, x1), ap (g, x1))
						)) )  )   ) ) ) )) ));
	*/
	flag_control = 0;
	TYPE_St = UNDEF;
	St->term.typ = TYPE_St;
	tmp[14] = ap (ap (c, x1), ap (g, x1)); trace_term (tmp[14]);
	tmp[12] = lambda (x1, tmp[14]); trace_term (tmp[12]);
	tmp[15] = ap (ap (T_PFNC, a), tmp[12]); trace_term (tmp[15]);
	tmp[18] = /*plambda*/ abst (g, tmp[15]); trace_term (tmp[18]);
	tmp[16] = ap (ap (T_PFNC, a), b); trace_term (tmp[16]);
	tmp[9] = ap (ap (T_PFNC, tmp[16]), tmp[18]); trace_term (tmp[9]);
	tmp[11] = ap (ap (T_PFNC, ap (b, x1)), ap (c, x1)); trace_term (tmp[11]);
	tmp[10] = lambda (x1, tmp[11]); trace_term (tmp[10]);
	tmp[8] = ap (ap (T_PFNC, a), tmp[10]); trace_term (tmp[8]);
	tmp[7] = ap (ap (T_FNC, tmp[8]), tmp[9]); trace_term (tmp[7]);
	tmp[6] = plambda (c, tmp[7]); trace_term (tmp[6]);
	tmp[5] = ap (ap (T_FNC, a), ap (ap (T_FNC, ap (b, x1)), T_TYPE));
		trace_term (tmp[5]);
	tmp[4] = ap (ap (T_PFNC, tmp[5]), tmp[6]); trace_term (tmp[4]);
	tmp[3] = /*abst*/ plambda (b, tmp[4]); trace_term (tmp[3]);
	tmp[2] = ap (ap (T_PFNC, ap( ap (T_FNC, a), T_TYPE)), tmp[3]); trace_term (tmp[2]);
	tmp[1] = lambda /*abst*/ (a, tmp[2]); trace_term (tmp[1]);
	TYPE_St = pfnc (TYPE, tmp[1]);
	St->term.typ = TYPE_St;
	trace_term (St);
	/* flag_control = 1; */

	/* Kt a:T b:a->T x:a y:bx = x:a
	   Kt: T->>\a. (a->T) ->>\b. a->>\x.bx->a */
	/* TYPE_Kt = pfnc (TYPE, lambda (a,
				ap (ap (T_PFNC, T_TYPE), lambda (b,
				    ap (ap (T_PFNC, a), lambda (x1,
					ap (ap (T_FNC, ap (b, x1)), a)
						)) )) )); */
	/*
	TYPE_Kt = pfnc (TYPE, lambda (a,
				ap (ap (T_PFNC, ap(a,T_TYPE)), plambda (b,
				    ap (ap (T_PFNC, a), plambda (x1,
					ap (ap (T_FNC, ap (b, x1)), a)
						)) )) ));
	*/
	tmp[6] = ap (ap (T_FNC, ap (b, x1)), a); trace_term (tmp[6]);
	tmp[5] = abst /*plambda*/ (x1, tmp[6]); trace_term (tmp[5]);
	tmp[4] = ap (ap (T_PFNC, a), tmp[5]); trace_term (tmp[4]);
	tmp[3] = abst /*plambda*/ (b, tmp[4]); trace_term (tmp[3]);
	tmp[2] = ap (ap (T_PFNC, ap (a, T_TYPE)), tmp[3]); trace_term (tmp[2]);
	tmp[1] = abst /*lambda*/ (a, tmp[2]); trace_term (tmp[1]);
	TYPE_Kt = pfnc (TYPE, tmp[1]);
	flag_control = 1;
	Kt->term.typ = TYPE_Kt;
	trace_term (Kt);

	/*
	TYPE_St = pfnc (TYPE, lambda (a,
			    ap (ap (T_PFNC, T_TYPE), lambda (b,
				ap (ap (T_PFNC, T_TYPE), lambda (c,
				    ap (ap (T_FNC,
					ap (ap (T_PFNC, a), lambda (x1,
						ap (ap (T_PFNC, ap(b,x1)),
							ap(c,x1))
								   )) ),
					ap (ap (T_FNC,
					    ap (ap (T_PFNC, a), b)
					       ),
					    ap (ap (T_PFNC, a), lambda (x1,
						ap (ap (c, x1), ap (b, x1))
								   ))
					   ) ) )) )) ));
	*/

	TYPE_REPt = pfnc (TYPE, lambda (a,
				ap (ap (T_FNC, a),
				    ap (ap (T_FNC,
					ap (ap (T_FNC, a), a)
					   ),
					ap (ap (T_FNC, T_ORD), a)
					) ) ));
	REPt->term.typ = TYPE_REPt;
	trace_term (REPt);

	TYPE_TEST = calcul_type_term (TEST);
	TEST->term.typ = TYPE_TEST;
	trace_term (TEST);

	Yt->term.typ = pfnc (TYPE, lambda (t,
			ap (ap (T_FNC, ap (ap (T_FNC, t), t)), t) ));
	trace_term (Yt);

#define axex(ax,tm) ax->k=DEM_AXIOM; ax->left=tm; ax->right=tm;
	axex (EX_ZERO, ZERO);
	axex (EX_SUC, SUC);
	axex (EX_LIM, LIM);
	axex (EX_UNDEF_TERM, UNDEF_TERM);
	axex (EX_It, It);
	axex (EX_Kt, Kt);
	axex (EX_St, St);
	axex (EX_Yt, Yt);
	axex (EX_TEST, TEST);
	axex (EX_REPt, REPt);

	axex (EX_ORD, T_ORD);
	axex (EX_UNDEF, T_UNDEF);
	axex (EX_TYPE, T_TYPE);
	axex (EX_FNC, T_FNC);
	axex (EX_PFNC, T_PFNC);

};

type fnc (type a, type b)
{
type f;
	ALLOC (f, struct type_fnc);
	f->k = TYPE_FNC;
	f->fnc.arg = a;
	f->fnc.res = b;
	return f;
}

type pfnc (type a, term b)
{
type f;
	ALLOC (f, struct type_pfnc);
	f->k = TYPE_PFNC;
	f->pfnc.arg = a;
	f->pfnc.res = b;
	return f;
}

type trm (term a)
{
type t;
	ALLOC (t, sizeof (struct type_trm));
	t->k = TYPE_TRM;
	t->trm.typ = a;
	return t;
}

term I (type a)
{
term i;
	ALLOC (i, struct term_I);
	i->k = TERM_I;
	i->I.a = a;
	i->term.typ = calcul_type_term (i);
	return i;
}

/*
dem EX_I (type a)
{
dem d;
	ALLOC (d, *d);
	d->k = DEM_AXIOM;
	d->left = I (a);
	d->right = d->right;
}
*/
#define def_exax(ax,params,tm)    \
dem ax params                   \
{                                  \
dem d;                              \
	ALLOC (d, *d);      \
	d->k = DEM_AXIOM;             \
	d->n_premisses = 0; \
	d->left = tm;                     \
	d->right = d->left;                  \
	return d; \
}

def_exax (EX_I, (type a), I(a))

term K (type a, type b)
{
term k;
	ALLOC (k, struct term_K);
	k->k = TERM_K;
	k->K.a = a;
	k->K.b = b;
	k->term.typ = calcul_type_term (k);
	return k;
}
def_exax (EX_K, (type a, type b), K(a,b))

term S (type a, type b, type c)
{
term s;
	ALLOC (s, struct term_S);
	s->k = TERM_S;
	s->S.a = a;
	s->S.b = b;
	s->S.c = c;
	s->term.typ = calcul_type_term (s);
	return s;
}
def_exax (EX_S, (type a, type b, type c), S(a,b,c))

term Y (type a)
{
term y;
	ALLOC (y, struct term_Y);
	y->k = TERM_Y;
	y->Y.a = a;
	y->term.typ = calcul_type_term (y);
	return y;
}
def_exax (EX_Y, (type a), Y(a))

term rep (type a)
{
term r;
	ALLOC (r, struct term_rep);
	r->k = TERM_REP;
	r->rep.a = a;
	r->term.typ = calcul_type_term (r);
	return r;
}
def_exax (EX_rep, (type a), rep(a))

term ap1 (term fnc, term arg)
{
term a;
type tf, ta, r;
	ALLOC (a, struct term_ap);
	a->k = TERM_AP;
	a->ap.fnc = fnc;
	a->ap.arg = arg;
	a->term.typ = calcul_type_term (a);
#if 0
	/* a->term.typ = type_term(fnc)->fnc.res; */
	tf = type_term (fnc);
			if (tf->k == TYPE_FNC)
				r = tf->fnc.res;
			else if (tf->k == TYPE_PFNC)
				r = type_from_term (canonic_term (
					ap (tf->pfnc.res, x->ap.arg) ));

			else
			/* if (tf->k != TYPE_FNC && tf->k != TYPE_PFNC) */
			{
				sput ("type_term: invalid function\n", err);
				r = UNDEF;
			}
	a->term.typ = r;
#endif
	return a;
}

term abst (term arg, term res)
{
term f; /*fnc*/
type t;
term tt;
	ALLOC (f, struct term_abst);
	f->k = TERM_ABST;
	f->abst.arg = arg;
	f->abst.res = res;
	t = type_term (res);
	tt = term_from_type (t);
	if (!occur (arg, tt))
		f->term.typ = fnc (type_term(arg), t);
	else
		f->term.typ = pfnc (type_term(arg), plambda (arg, tt));
	return f;
}

int equal_type_1 (type a, type b)
{
	if (a->k != b->k)
		return 0;
	if (a->k == TYPE_FNC)
	{
	    if (!equal_type (a->fnc.arg, b->fnc.arg))
		return 0;
	    if (!equal_type (a->fnc.res, b->fnc.res))
		return 0;
	    return 1;
	}
	if (a->k == TYPE_PFNC)
	{
	    if (!equal_type (a->pfnc.arg, b->pfnc.arg))
		return 0;
	    if (!equal_term (a->pfnc.res, b->pfnc.res))
		return 0;
	    return 1;

	}
	return 1;
}

int equal_term_1 (term x, term y)
{
	if (x->k != y->k)
		return 0;
	if (x->k == TERM_AP)
	{
		if (!equal_term (x->ap.fnc, y->ap.fnc))
			return 0;
		if (!equal_term (x->ap.arg, y->ap.arg))
			return 0;
		return 1;
	}
	if (x->k == TERM_ABST)
	{
		if (!equal_term (x->abst.arg, y->abst.arg))
			return 0;
		if (!equal_term (x->abst.res, y->abst.res))
			return 0;
		return 1;
	}
	if (x->k == TERM_VAR)
		return !strcmp (x->var.name, y->var.name);
	return 1;
}

term canonic_term_0 (term x);

term subst (term v, term res, term arg)
{
	if (equal_term (v, res))
		return arg;
	if (!occur(v,res))
		return res;
	if (res->k == TERM_AP)
		return ap (subst (v, res->ap.fnc, arg),
				subst (v, res->ap.arg, arg));
	if (res->k == TERM_ABST)
	{
		if (equal_term (v, res->abst.arg))
			return res;
		return abst (res->abst.arg, subst (v, res->abst.res, arg));
	}
	return res;
}

#define canonic_term
term canonic_term_1 (term x)
{
	if (x->k != TERM_AP)
		return x;
	if (x->ap.fnc->k == TERM_I)
		return canonic_term (x->ap.arg);
	if (x->ap.fnc->k == TERM_ABST)
		return subst (x->ap.fnc->abst.arg, x->ap.fnc->abst.res,
			x->ap.arg);
	if (x->ap.fnc->k != TERM_AP)
		return x;
	if (x->ap.fnc->ap.fnc->k == TERM_It)
		return canonic_term (x->ap.arg);
	if (x->ap.fnc->ap.fnc->k == TERM_K)
		return canonic_term (x->ap.fnc->ap.arg);
	if (x->ap.fnc->ap.fnc->k != TERM_AP)
		return x;
	if (x->ap.fnc->ap.fnc->ap.fnc->k == TERM_S)
	return canonic_term (ap (ap (canonic_term (x->ap.fnc->ap.fnc->ap.arg),
					canonic_term (x->ap.arg)),
				ap (canonic_term (x->ap.fnc->ap.arg),
					canonic_term (x->ap.arg) )  ));
	/* reste cas It, Kt, St, TEST */
	if (x->ap.fnc->ap.fnc->ap.fnc->k != TERM_AP)
		return x;
	if (x->ap.fnc->ap.fnc->ap.fnc->ap.fnc->k == TERM_It)
		return canonic_term (x->ap.fnc->ap.arg);
	if (x->ap.fnc->ap.fnc->ap.fnc->ap.fnc->k == TERM_TEST)
	{
	term n;
		n = x->ap.fnc->ap.fnc->ap.arg;
		n = canonic_term (n);
		if (equal_term (n, /*TERM_*/ZERO))
			return x->ap.fnc->ap.arg;
		if (n->k != TERM_AP)
			return x;
		if (n->ap.fnc->k != TERM_SUC)
			return x;
		return ap (x->ap.arg, n);

	}
	if (x->ap.fnc->ap.fnc->ap.fnc->ap.fnc->k != TERM_AP)
		return x;
	if (x->ap.fnc->ap.fnc->ap.fnc->ap.fnc->ap.fnc->k != TERM_AP)
		return x;
	if (x->ap.fnc->ap.fnc->ap.fnc->ap.fnc->ap.fnc->ap.fnc->k == TERM_St)
		return canonic_term (ap (ap (canonic_term (x->ap.fnc->ap.fnc->ap.arg),
					canonic_term (x->ap.arg)),
				ap (canonic_term (x->ap.fnc->ap.arg),
					canonic_term (x->ap.arg) )  ));

	return x;

}
#undef canonic_term

#if 0
term canonic_term_0 (term x)
{
term y;
	y = canonic_term_1 (x);
	if (y != x)
		return y;
	if (x->k == TERM_AP)
	{
		y = ap (canonic_term_0 (x->ap.fnc),
			canonic_term_0 (x->ap.arg));
		if (equal_term_1 (y, x))
			return y;
		y = canonic_term_0 (y);
	}
	if (x->k == TERM_ABST)
	{
		y = abst (x->abst.arg, canonic_term_0 (x->ap.res));
	}
	return y;
}
#else

term canonic_term_int (term x, int *flag_modif)
{
term y, f, a, r;
int fmf, fma, fmr;
	y = canonic_term_1 (x);
	if (y != x)
	{
		if (flag_modif)
			*flag_modif = 1;
		return y;
	}
	if (x->k == TERM_AP)
	{
		f = canonic_term_int (x->ap.fnc, &fmf);
		a = canonic_term_int (x->ap.arg, &fma);
		if (fmf == 0 && fma == 0)
		{
			if (flag_modif)
				*flag_modif = 0;
			return x;
		}
		else
		{
			if (flag_modif)
				*flag_modif = 1;
			return ap (f, a);
		}
	}
	if (x->k == TERM_ABST)
	{
		r = canonic_term_int (x->abst.res, &fmr);
		if (fmr == 0)
		{
			if (flag_modif)
				*flag_modif = 0;
			return x;
		}
		else
		{
			if (flag_modif)
				*flag_modif = 1;
			return abst (x->abst.arg, r);
		}
	}
	if (flag_modif)
		*flag_modif = 0;
	return x;

}

term canonic_term_0 (term x)
{
int modif;
	do
		x = canonic_term_int (x, &modif);
	while (modif);
	return x;
}

#endif

term canonic_term (term x)
{
term y;
#ifdef TRACE1
	sput ("\nReduction of ", err);
	write_term (x, err);
	sput (" ...", err);
#endif
	y = canonic_term_0 (x);
#ifdef TRACE1
	sput ("\nReduction of ", err);
	write_term (x, err);
	sput (" --> ", err);
	write_term (y, err);
#endif
	return y;
}

type canonic_type (type t)
{
type t1;
term x;
	if (t->k != TYPE_TRM)
		return t;
	x = canonic_term (t->trm.typ);
	t1 = type_from_term (x);
	return t1;
}

int equal_type (type a, type b)
{
	return equal_type_1 (canonic_type (a), canonic_type (b));
}

int equal_term (term x, term y)
{
	return equal_term_1 (canonic_term (x), canonic_term (y));
}

term var (char *name, type t)
{
term v;
	ALLOC (v, struct term_var);
	v->k = TERM_VAR;
	v->var.name = name;
	v->var.typ = t;
	v->term.typ = t;
	return v;
}

def_exax (EX_var, (char *name, type t), var(name,t))


write_type (type t, struct put_fnct *put)
{
	switch (t->k)
	{
		case TYPE_ORD:
			sput ("O", put);
			break;
		case TYPE_TYPE:
			sput ("T", put);
			break;
		case TYPE_FNC:
			if (t->fnc.arg->k == TYPE_FNC ||
				t->fnc.arg->k == TYPE_PFNC)
				sput ("(", put);
			write_type (t->fnc.arg, put);
			if (t->fnc.arg->k == TYPE_FNC ||
				t->fnc.arg->k == TYPE_PFNC)
				sput (")", put);
			sput ("->", put);
			write_type (t->fnc.res, put);
			break;
		case TYPE_PFNC:
			if (t->pfnc.arg->k == TYPE_FNC ||
				t->pfnc.arg->k == TYPE_PFNC)
				sput ("(", put);
			write_type (t->pfnc.arg, put);
			if (t->pfnc.arg->k == TYPE_FNC ||
				t->pfnc.arg->k == TYPE_PFNC)
				sput (")", put);
			sput ("->>", put);
			write_term (t->pfnc.res, put);
			break;
		case TYPE_TRM:
			sput ("{", put);
			write_term (t->trm.typ, put);
			sput ("}", put);
			break;
		case TYPE_UNDEF:
			sput (" ? ", put);
			break;
		default:
			sput ("???", put);
	}
}

write_term (term x, struct put_fnct *put)
{
	switch (x->k)
	{
		case TERM_I:
			sput (" I [", put);
			write_type (x->I.a, put);
			sput ("] ", put);
			break;
		case TERM_K:
			sput (" K [", put);
			write_type (x->K.a, put);
			sput (", ", put);
			write_type (x->K.b, put);
			sput ("] ", put);
			break;
		case TERM_S:
			sput (" S [", put);
			write_type (x->S.a, put);
			sput (", ", put);
			write_type (x->S.b, put);
			sput (", ", put);
			write_type (x->S.c, put);
			sput ("] ", put);
			break;
		case TERM_Y:
			sput (" Y [", put);
			write_type (x->Y.a, put);
			sput ("] ", put);
			break;
		case TERM_ZERO:
			sput (" 0 ", put);
			break;
		case TERM_SUC:
			sput (" suc ", put);
			break;
		case TERM_LIM:
			sput (" lim ", put);
			break;
		case TERM_REP:
			sput (" rep [", put);
			write_type (x->rep.a, put);
			sput ("] ", put);
			break;
		case TERM_AP:
			sput ("-", put);
			write_term (x->ap.fnc, put);
			write_term (x->ap.arg, put);
			break;
		case TERM_VAR:
			sput (" <", put);
			sput (x->var.name, put);
			/*
			sput (":", put);
			write_type (x->var.typ, put);
			*/
			sput ("> ", put);
			break;
		case TERM_ABST:
			sput (" \\", put);
			write_term (x->abst.arg, put);
			sput (".(", put);
			write_term (x->abst.res, put);
			sput (")", put);
			break;
		case TERM_UNDEF:
			sput (" U ", put);
			break;
		case TERM_It:
			sput (" It ", put);
			break;
		case TERM_Kt:
			sput (" Kt ", put);
			break;
		case TERM_St:
			sput (" St ", put);
			break;
		case TYPE_ORD:
			sput (" O ", put);
			break;
		case TYPE_TYPE:
			sput (" T ", put);
			break;
		/*
		case TYPE_UNDEF:
			sput (" U ", put);
			break; */
		case TYPE_FNC:
			sput (" F ", put);
			break;
		case TYPE_PFNC:
			sput (" f ", put);
			break;
		case TERM_TEST:
			sput (" ? ", put);
			break;
		case TERM_REPt:
			sput (" rep ", put);
			break;
		default:
			sput ("???", put);

	}
}

#undef TRACE_TERM
/*#define trace_term(x)*/

type type_term_1 (term x)
{
term t, a, b, c, x1, n;
type r;
term tmp[40];
	t = var ("t", TYPE);
	a = var ("a", TYPE);
	b = var ("b", TYPE);
	c = var ("c", TYPE);
	x1 = var ("x1", TYPE);
	n = var ("n", ORD);

	switch (x->k)
	{
		case TERM_I/**/: 	/* a->a */
			/* return fnc (x->I.a, x->I.a); */
			r = fnc (x->I.a, x->I.a);
			break;
		case TERM_K:    /* a->(b->a) */
			r = fnc (x->K.a, fnc (x->K.b, x->K.a));
			break;
		case TERM_S:	/* (a->b->c) -> (a->b) -> a -> c */
			r = fnc (fnc (x->S.a, fnc (x->S.b, x->S.c)),
				fnc (fnc (x->S.a, x->S.b),
					fnc (x->S.a, x->S.c)));
			break;
		case TERM_Y:
			r = fnc (fnc (x->Y.a, x->Y.a), x->Y.a);
			break;
		case TERM_ZERO:
			r = ORD;
			break;
		case TERM_SUC:
			r = fnc (ORD, ORD);
			break;
		case TERM_LIM:
			r = fnc (fnc (ORD, ORD), ORD);
			break;
		case TERM_REP:
			r = fnc (ORD, fnc (fnc (x->rep.a, x->rep.a),
						fnc (x->rep.a, x->rep.a)));
			break;
		case TERM_AP:
		{
		type tf;
			tf = type_term (x->ap.fnc);
			if (tf->k == TYPE_FNC)
				r = tf->fnc.res;
			else if (tf->k == TYPE_PFNC)
				r = type_from_term (canonic_term (
					ap (tf->pfnc.res, x->ap.arg) ));

			else
			/* if (tf->k != TYPE_FNC && tf->k != TYPE_PFNC) */
			{
			    if (flag_control)
				sput ("type_term: invalid function\n", err);
			    r = UNDEF;
			}
			/*
			else
				r = tf->fnc.res;*/

		}
		break;
		case TERM_VAR:
			r = x->var.typ;
			break;
		case TERM_ABST:
{
type t;
term tt, f;
	t = type_term (x->abst.res);
	tt = term_from_type (t);
	if (!occur (x->abst.arg, tt))
		/*f->term.typ*/ r = fnc (type_term(x->abst.arg), t);
	else
		r = pfnc (type_term(x->abst.arg),
					plambda (x->abst.arg, tt));
}
			break;
		case TERM_It: /* t:T -> I[t]:t->t */
			/* r = pfnc (TYPE, lambda (t, ap (ap (T_FNC, t), t))); */
			r = TYPE_It;
			break;
		case TERM_Kt: /* a:T -> b:T -> K[a,b]: a->>\x.bx->a */
			/* r = pfnc (TYPE, lambda (a,
				ap (ap (T_PFNC, T_TYPE), lambda (b,
					ap (ap (T_PFNC, a), lambda (x1,
						ap (ap (T_FNC, ap (b, x1)), a)
						)) )) )); */
			r = TYPE_Kt;
			break;
		case TERM_St:
		/* a:T -> b:T -> c:T -> S[a,b,c]:
			(a->>\x.(bx->>cx)) -> (a->>b) -> a ->>\x.cx(bx) */
			/* r = pfnc (TYPE, lambda (a,
			    ap (ap (T_PFNC, T_TYPE), lambda (b,
				ap (ap (T_PFNC, T_TYPE), lambda (c,
				    ap (ap (T_FNC,
					ap (ap (T_PFNC, a), lambda (x1,
						ap (ap (T_PFNC, ap(b,x1)),
							ap(c,x1))
								   )) ),
					ap (ap (T_FNC,
					    ap (ap (T_PFNC, a), b)
					       ),
					    ap (ap (T_PFNC, a), lambda (x1,
						ap (ap (c, x1), ap (b, x1))
								   ))
					   ) ) )) )) )); */
			r = TYPE_St;
			break;

		case TYPE_ORD:
		case TYPE_TYPE:
			r = TYPE;
			break;
		case TYPE_FNC:
			/* r = fnc (TYPE, fnc (TYPE, TYPE)); */
			r = TYPE_TFNC;
			break;
		case TYPE_PFNC:
			/* r = pfnc (TYPE, lambda (t,
				ap (ap (T_FNC,
					ap (ap (T_FNC, t), T_TYPE)
					), T_TYPE)
					  )); */
			r = TYPE_TPFNC;
			break;
		case TERM_TEST:
			FREE (a);
			a = var ("a", fnc(ORD,TYPE));
			/*
			r = pfnc (fnc(ORD,TYPE), lambda (a,
				ap (ap (T_PFNC, T_ORD), lambda (n,
				    ap (ap (T_FNC, ap (a, n)),
					ap (ap (T_FNC,
					    ap (ap (T_FNC, ORD), ap (a, n))
					       ), ap (a, n)) ) )) ));
			*/

			tmp[9] = ap (a, n);
				trace_term (tmp[9]);
			tmp[10] = ap (T_FNC, T_ORD); trace_term (tmp[10]);
			tmp[8] = ap (tmp[10], tmp[9]); trace_term (tmp[8]);
			tmp[7] = ap (ap (T_FNC, tmp[8]), tmp[9]);
				trace_term (tmp[7]);
			tmp[6] = ap (T_FNC, tmp[9]); trace_term (tmp[6]);
			tmp[5] = ap (tmp[6], tmp[7]); trace_term (tmp[5]);
			tmp[4] = lambda (n, tmp[5]); trace_term (tmp[4]);
			tmp[3] = ap (T_PFNC, T_ORD);
				trace_term (tmp[3]);
			tmp[2] = ap (tmp[3], tmp[4]); trace_term (tmp[2]);
			tmp[1] = lambda (a, tmp[2]); trace_term (tmp[1]);
			r = pfnc (fnc(ORD,TYPE), tmp[1]);
			break;
		case TERM_REPt:
			/* r = pfnc (TYPE, lambda (a,
				ap (ap (T_FNC, a),
				    ap (ap (T_FNC,
					ap (ap (T_FNC, a), a)
					   ),
					ap (ap (T_FNC, ORD), a)
					) ) )); */
			r = TYPE_REPt;
		default:
			r = UNDEF;
	}
/*
	FREE (t);
	FREE (a);
	FREE (b);
	FREE (c);
	FREE (x1);
	FREE (n);
*/
	return r;
}

type calcul_type_term (term x)
{
type t;
#ifdef TRACE_TYPE
	sput ("Type of ", err);
	write_term (x, err);
	sput ("...\n", err);
#endif
	t = type_term_1 (x);
#ifdef TRACE_TYPE
	sput ("type of ", err);
	write_term (x, err);
	sput ("is ", err);
	write_type (t, err);
	sput (".\n", err);
#endif
	return t;
}

type type_term (term x)
{
	return x->term.typ;
}

term ap (term fnc, term arg)
{
type tf, ta;
	if (!flag_control)
		return ap1 (fnc, arg);
	tf = type_term (fnc);
	if (tf->k != TYPE_FNC && tf->k != TYPE_PFNC)
    		sput ("ap: invalid function\n", err);
	ta = type_term (arg);
	if (!equal_type (ta, tf->fnc.arg))
	{
		sput ("ap: bad type\n\tfunction ", err);
		write_term (fnc, err);
		sput (" has type ", err);
		write_type (tf, err);
		sput ("\n\targument ", err);
		write_term (arg, err);
		sput (" has type ", err);
		write_type (ta, err);
		sput ("\n", err);
	}
	/* if (tf->k == TYPE_FNC) */
		return ap1 (fnc, arg);

}

term apt (dem d, term fnc, term arg)
{
type tf, ta;
	if (!flag_control)
		return ap1 (fnc, arg);
	tf = type_term (fnc);
	ta = type_term (arg);
	if (!equal_term (term_from_type (tf), d->left))
	{
		sput ("\napt: type of function differs from left of dem\n",
			err);
		sput ("\ttype of function : ", err);
		write_type (tf, err);
		sput ("\n\tdem : ", err);
		write_term (d->left, err);
		sput (" = ...\n", err);
		/*return ap1 (fnc, arg);*/
	}
	tf = type_from_term (d->right);


	if (tf->k != TYPE_FNC && tf->k != TYPE_PFNC)
		sput ("apt: invalid function\n", err);
	if (!equal_type (ta, tf->fnc.arg))
	{
		sput ("apt: bad type\n\tfunction ", err);
		write_term (fnc, err);
		sput (" has type ", err);
		write_type (tf, err);
		sput ("\n\targument ", err);
		write_term (arg, err);
		sput (" has type ", err);
		write_type (ta, err);
		sput ("\n", err);
	}
	/* if (tf->k == TYPE_FNC) */
		return ap1 (fnc, arg);

}

int occur (term v, term x)
{
	if (x->k == TERM_VAR && !strcmp (x->var.name, v->var.name) &&
		equal_type (x->var.typ, v->var.typ))
		return 1;
	/*if (x->k != TERM_AP)
		return 0;*/
	if (x->k == TERM_AP)
	{
		if (occur (v, x->ap.fnc))
			return 1;
		if (occur (v, x->ap.arg))
			return 1;
	}
	if (x->k == TERM_ABST)
	{
		if (equal_term (v, x->abst.arg))
			return 0;
		if (occur (v, x->abst.res))
			return 1;
	}

	return 0;
}


term lambda_1 (term v, term x)
{
term f, a, ttf, tta, t1;
type tf, ta, t;
	if (v->k != TERM_VAR)
	{
		sput ("lambda: 1st arg not variable\n", err);
		/* return UNDEF_TERM; */
		return abst (v, x);
	}
	if (x->k == TERM_VAR && !strcmp (x->var.name, v->var.name) &&
		equal_type (x->var.typ, v->var.typ))
		return I (v->var.typ);
	if (!occur (v, x))
		return ap (K (type_term (x), v->var.typ), x);
	if (x->k /*== TERM_ABST*/ != TERM_AP)
	{
		return abst (v, x);
	}
	f = x->ap.fnc;
	a = x->ap.arg;
	if (a->k == TERM_VAR && !strcmp (a->var.name, v->var.name) &&
		equal_type (a->var.typ, v->var.typ) &&
		!occur (v, f))
		return f;
	tf = type_term (f);
	ta = type_term (a);
	ttf = term_from_type (tf);
	tta = term_from_type (ta);
	/* t = term_from_type (tf->fnc.res); */
	if (!occur (v, ttf) && !occur (v, tta) && tf->k == TYPE_FNC)
	    return ap (ap (S (v->var.typ, ta, tf->fnc.res),
			lambdax (v, f)),
				lambdax (v, a));
	if (tf->k == TYPE_FNC)
	    t1 = term_from_type (tf->fnc.res);
	else if (tf->k == TYPE_PFNC)
	    /* t = ap (tf->pfnc.res, a); */
	    t1 = tf->pfnc.res;
	else
	{
	    if (flag_control)
	    {
		sput ("\nlambda_1: invalid function type", err);
		sput ("\n\tfunction ", err);
		write_term (f, err);
		sput ("\n\thas type ", err);
		write_type (tf, err);
		sput ("\n\tapplied to ", err);
		write_term (a, err);
		sput ("\n", err);
	    }
		/*return UNDEF_TERM;*/
	    return abst (v, x);
	}
	return ap (ap (ap (ap (ap (St, term_from_type(v->var.typ)),
							lambdax (v, tta)),
					lambdax (v, t1)),
		lambdax (v, f)),
			lambdax (v, a));

}

term lambda (term v, term x)
{
	return abst (v, x);
}

term plambda (term v, term x)
{
	return abst (v, x);
}

term lambdax (term v, term x)
{
term r;
#ifdef TRACE
	sput ("Lambda ", err);
	write_term (v, err);
	sput (" . ", err);
	write_term (x, err);
	sput ("...\n", err);
#endif
	r = lambda_1 (v, x);
#ifdef TRACE
	sput ("lambda ", err);
	write_term (v, err);
	sput (" . ", err);
	write_term (x, err);
	sput (" = ", err);
	write_term (r, err);
	sput (".\n", err);
#endif
	return r;
}

term plambdax (term v, /*type t,*/ term x)
{
term f, a, ttf, tta, t1;
type tf, ta, t;
	/* v->var.typ = t; */
	if (v->k != TERM_VAR)
	{
		sput ("lambda: 1st arg not variable\n", err);
		return UNDEF_TERM;
	}
	if (x->k == TERM_VAR && !strcmp (x->var.name, v->var.name) &&
		equal_type (x->var.typ, v->var.typ))
		return ap (It, term_from_type (v->var.typ));
	if (!occur (v, x))
		return ap (ap (ap (Kt, term_from_type (type_term (x))),
					term_from_type (v->var.typ)), x);
	if (x->k != TERM_AP)
		return abst (v, x);
	f = x->ap.fnc;
	a = x->ap.arg;
	if (a->k == TERM_VAR && !strcmp (a->var.name, v->var.name) &&
		equal_type (a->var.typ, v->var.typ) &&
		!occur (v, f))
		return f;
	tf = type_term (f);
	ta = type_term (a);
	ttf = term_from_type (tf);
	tta = term_from_type (ta);
	if (tf->k != TYPE_FNC)
	{
		if (flag_control)
		{
			sput ("plambda: bad function type\n\tfunction ", err);
			write_term (f, out);
			sput ("\n\thas type ", out);
			write_type (tf, out);
			sput ("\n", out);
		}
		return abst (v, x);
	}
	t1 = term_from_type (tf->fnc.res);
	if (!occur (v, ttf) && !occur (v, tta))
	{
	term tmp[30];
		trace_term (v);
		trace_term (f);
		trace_term (a);
		tmp[1] = term_from_type (v->var.typ);
		trace_term (tmp[1]);
		tmp[2] = term_from_type (ta);
		trace_term (tmp[2]);
		tmp[3] = term_from_type (tf->fnc.res);
		trace_term (tmp[3]);
		tmp[4] = plambdax (v, f);
		trace_term (tmp[4]);
		tmp[5] = plambdax (v, a);
		trace_term (tmp[5]);
		/*
		tmp[6] = ap (ap (ap (ap (ap (St,
			tmp[1]), tmp[2]), tmp[3]), tmp[4]), tmp[5]);
		trace_term (tmp[6]);
		*/
		tmp[7] = ap (K (TYPE, /*tmp[1]*/ v->var.typ), tmp[2]);
		trace_term (tmp[7]);
		tmp[8] = ap (K (fnc(/*tmp[2]*/ta, TYPE), /*tmp[1]*/
					v->var.typ),
				ap (K (TYPE, ta), tmp[3]));
		trace_term (tmp[8]);
		tmp[9] = ap (ap (ap (ap (ap (St,
			tmp[1]), tmp[7]), tmp[8]), tmp[4]), tmp[5]);
		trace_term (tmp[9]);
		return tmp[9];
	}
#if 0
	    return ap (ap (
	    /* S (v->var.typ, ta, tf->fnc.res), */
	    ap (ap (ap (St, term_from_type (v->var.typ)),
		term_from_type (ta)),
			term_from_type (tf->fnc.res)),
			lambda (v, f)),
				lambda (v, a));
#endif
/*
	return ap (ap (ap (ap (ap (St, term_from_type(v->var.typ)),
							lambda (v, tta)),
				lambda (v, ap (K(TYPE,v->var.typ), t))),
		lambda (v, f)),
			lambda (v, a));
*/
	return ap (ap (ap (ap (ap (St, term_from_type(v->var.typ)),
							plambdax (v, tta)),
				plambdax (v, ap (K(TYPE,v->var.typ), t1))),
		plambdax (v, f)),
			plambdax (v, a));

}
/* #define TRACE_TERM */
#define trace_term(_x) \
{ \
char buftrace[50]; \
	sprintf (buftrace, "%s(%d) [%X,%X]: ", \
		__FILE__, __LINE__, 0, 0); \
	_t = type_term (_x);                    \
	sput ("\nType of " #_x " = ", out); \
	write_term (_x, out);                \
	sput (" is ", out);                  \
	write_type (_t, out);                \
}


term term_from_type (type t)
{
static char buf[1000];
	switch (t->k)
	{
		case TYPE_ORD:
			return T_ORD;
		case TYPE_TYPE:
			return T_TYPE;
		case TYPE_UNDEF:
			return T_UNDEF;
		case TYPE_FNC:
			return ap (ap (T_FNC, term_from_type (t->fnc.arg)),
				term_from_type (t->fnc.res));
		case TYPE_PFNC:
			return ap (ap (T_PFNC, term_from_type (t->pfnc.arg)),
				t->pfnc.res);
		case TYPE_TRM:
			return t->trm.typ;
		default:
			sprintf (buf, "\nterm_from_type: invalid type 0x%X",
					t->k);
			sput (buf, err);
			return UNDEF_TERM;
	}
}

type type_from_term (term x)
{
	x = canonic_term (x);
	switch (x->k)
	{
		case TYPE_ORD:
			return ORD;
		case TYPE_UNDEF:
			return UNDEF;
		case TYPE_TYPE:
			return TYPE;
		case TERM_AP:
			if (x->ap.fnc->k != TERM_AP)
				return trm(x);
			switch (x->ap.fnc->ap.fnc->k)
			{
				case TYPE_FNC:
				/*
					return fnc (type_from_term (
						x->ap.fnc->ap.arg),
					 type_from_term(x->ap.arg));*/
				{
				type ta, tr, tf;
					ta = type_from_term (x->ap.fnc->ap.arg);
#ifdef TRACE
					sput ("\nta = ", out);
					write_type (ta, out);
#endif
					tr = type_from_term (x->ap.arg);
#ifdef TRACE
					sput ("\ntr = ", out);
					write_type (tr, out);
#endif
					tf = fnc (ta, tr);
#ifdef TRACE
					sput ("\ntf = ", out);
					write_type (tf, out);
#endif
					return tf;
				}
				case TYPE_PFNC:
					return pfnc (type_from_term(
							x->ap.fnc->ap.arg),
						x->ap.arg);
				default:
					return trm (x);
			}

		default:
			return trm(x);
	}
}

line (int n, struct put_fnct *put)
{
int i;
	sput ("\n", put);
	for (i=0; i<n; i++)
		sput (" ", put);
}

write_dem (dem d, struct put_fnct *put, int l)
{
int i;
char buf[200];
	line (l, put);
	sprintf (buf, "DEM %c : ", d->k);
	sput (buf, put);
	write_term (d->left, put);
	line (l, put);
	sput ("      = ", put);
	write_term (d->right, put);
	line (l, put);
	sprintf (buf, "%d premisses : ", d->n_premisses);
	sput (buf, put);
	for (i=0; i<d->n_premisses; i++)
		write_dem (d->premisse[i], put, l+1);
	sput ("\n", put);
}


/*#define DEM_AXIOM 'A'*/
/* #define DEM_SYM 'x'	/* a=b => b=a */
dem dmsym (dem d1)
{
dem d;
	ALLOC (d, *d);
	d->k = DEM_SYM;
	d->n_premisses = 1;
	d->premisse[0] = d1;
	d->left = d1->right;
	d->right = d1->left;
	return d;
}

/* #define DEM_TRANS 't'	/* a=b, b=c => a=c */
dem dmtrans (dem d1, dem d2)
{
dem d;
	ALLOC (d, *d);
	if (equal_term (d1->right, d2->left))
	{
		d->k = DEM_TRANS;
		d->n_premisses = 2;
		d->premisse[0] = d1;
		d->premisse[1] = d2;
		d->left = d1->left;
		d->right = d2->right;
		return d;

	}
	else
	{
		sput ("\nInvalid transitivity: \n\t", err);
		write_term (d1->left, err);
		sput (" = ", err);
		write_term (d1->right, err);
		sput ("\n\t", err);
		write_term (d2->left, err);
		sput (" = ", err);
		write_term (d2->right, err);
		sput ("\n", err);
		exit (-1);
	}
}

/* #define DEM_AP 'a'	/* f:A->B=g:A->B, a:A=b:A => fa:B=gb:B */
dem dmap (dem d1, dem d2)
{
dem d;
type tf, tg, ta, tb;

	sput ("\ndmap: d1 = ", trc);
	write_dem (d1, trc, 1);
	sput ("\n      d2 = ", trc);
	write_dem (d2, trc, 1);

	ALLOC (d, *d);

	tf = type_term (d1->left);
	tg = type_term (d1->right);
	ta = type_term (d2->left);
	tb = type_term (d2->right);
/*
	if (tf->k == TYPE_FNC)
	{
		if (!equal_type (tf->fnc.arg, ta))
		{
		bad_type:
			sput ("\ndap: bad type\n\t", err);
			exit (-1);
		}
	}
*/
	if ((tf->k == TYPE_FNC || tf->k == TYPE_PFNC) &&
		equal_type (tf->fnc.arg, ta) &&
		(tg->k == TYPE_FNC || tg->k == TYPE_PFNC) &&
		equal_type (tg->fnc.arg, tb))
	{
		d->k = DEM_AP;
		d->n_premisses = 2;
		d->premisse[0] = d1;
		d->premisse[1] = d2;
		d->left = ap (d1->left, d2->left);
		d->right = ap (d1->right, d2->right);
		return d;
	}
	else
	{
		sput ("\ndap: bad type\n\t", err);
		exit (-1);
	}
}

/* #define DEM_APt 'a'     /* A:T=A' f:A->B=g a:A'=b => fa=gb */
dem dmapt (dem dtl, dem dtr, dem d1, dem d2)
{
dem d;
type tf, tg, ta, tb;

	ALLOC (d, *d);

	tf = type_term (d1->left);
	tg = type_term (d1->right);
	ta = type_term (d2->left);
	tb = type_term (d2->right);

	if ((tf->k == TYPE_FNC || tf->k == TYPE_PFNC) &&
		equal_term (term_from_type (tf->fnc.arg),
			dtl->left) &&
		equal_term (dtr->right,
			term_from_type(ta)) &&
		(tg->k == TYPE_FNC || tg->k == TYPE_PFNC) &&
		equal_type (tg->fnc.arg, tb))
	{
		d->k = DEM_AP;
		d->n_premisses = 2;
		d->premisse[0] = d1;
		d->premisse[1] = d2;
		d->left = ap (d1->left, d2->left);
		d->right = ap (d1->right, d2->right);
		return d;
	}
	else
	{
		sput ("\ndap: bad type\n\t", err);
		exit (-1);
	}
}

/* #define DEM_I 'I'	/* a:A=a' => I[A]a=a' */
dem dmI (dem d1)
{
dem d;
	ALLOC (d, *d);
	d->k = DEM_I;
	d->n_premisses = 1;
	d->premisse[0] = d1;
	d->left = ap (I(type_term(d1->left)), d1->left);
	d->right = d1->right;
	return d;
}

/* #define DEM_K 'K'	/* a:A=a', b:B=b' => K[A,B]ab = a' */
dem dmK (dem a, dem b)
{
dem d;
	ALLOC (d, *d);
	d->k = DEM_K;
	d->n_premisses = 2;
	d->premisse[0] = a;
	d->premisse[1] = b;
	d->left = ap (ap (K(type_term(a->left),type_term(b->left)),
				a->left), b->left);
	d->right = a->right;
	return d;
}

/* #define DEM_S 'S'	/* a:A->B->C=a', b:A->B=b', c:A=c' =>
				S[A,B,C]abc = a'c'(b'c') */
dem dmS (dem a, dem b, dem c)
{
dem d;
type tA, tB, tC, t;
	ALLOC (d, *d);
	d->k = DEM_S;
	d->n_premisses = 3;
	d->premisse[0] = a;
	d->premisse[1] = b;
	d->premisse[2] = c;
	tA = type_term (c->left);
	t = type_term (b->left);
	if (t->k != TYPE_FNC)
	{
		sput ("\ndms: bad type\n", err);
		exit (-1);
	}
	tB = t->fnc.res;
	t = type_term (a->left);
	if (t->k != TYPE_FNC)
	{
		sput ("\ndms: bad type\n", err);
		exit (-1);
	}
	t = t->fnc.res;
	if (t->k != TYPE_FNC)
	{
		sput ("\ndms: bad type\n", err);
		exit (-1);
	}
	tC = t->fnc.res;
	d->left = ap (ap (ap (S(tA,tB,tC), a->left), b->left), c->left);
	d->right = ap (ap (a->right, c->right), ap (b->right, c->right));
	return d;
}

/* #define DEM_Y 'Y'	/* f:A->A=g => Y[A]f = f(Y[A]f) */
dem dmY (dem f)
{
dem d;
type t;
	ALLOC (d, *d);
	d->k = DEM_Y;
	d->n_premisses = 1;
	d->premisse[0] = f;
	t = type_term (f->left);
	if (t->k != TYPE_FNC)
	{
		sput ("\ndmY: bad type\n", err);
		exit (-1);
	}
	if (!equal_type (t->fnc.arg, t->fnc.res))
	{
		sput ("\ndmY: bad type\n", err);
		exit (-1);
	}
	d->left = ap (Y(t->fnc.res), f->left);
	d->right = ap (f->right, ap (Y(t->fnc.res), f->right));
	return d;
}

/* #define DEM_It 'i'	/* a:A=a' => iAa=a' */
dem dmIt (dem d1)
{
dem d;
	ALLOC (d, *d);
	d->k = DEM_It;
	d->n_premisses = 1;
	d->premisse[0] = d1;
	d->left = ap (ap (It, term_from_type (type_term (d1->left))),
			d1->left);
	d->right = d1->right;
	return d;
}

/* #define DEM_Kt 'k'	/* a:A=a', b:Ba=b' => kABab = a' */

dem dmKt (dem a, dem b)
{
dem d;
term tA, tB;
term t, t_b;
	ALLOC (d, *d);
	d->k = DEM_Ktt;
	d->n_premisses = 2;
	d->premisse[0] = a;
	d->premisse[1] = b;

	tA = term_from_type (type_term (a->left));
	t_b = term_from_type (type_term (b->left));
	if (t_b->k != TERM_AP)
	{
	bad_type:
		sput ("\ndmKt: bad type\n", err);
		exit (-1);
	}
	if (!equal_term (t_b->ap.arg, a->left))
		goto bad_type;
	tB = t_b->ap.fnc;

	d->left = ap (ap (ap (ap (Kt, tA), tB), a->left), b->left);
	d->right = a->right;
	return d;
}

dem dmKtt (dem dt /* Ba = type(b) */, dem a, dem b)
{
dem d;
term tA, tB;
term t, t_b;
	ALLOC (d, *d);
	d->k = DEM_Ktt;
	d->n_premisses = 3;
	d->premisse[0] = dt;
	d->premisse[1] = a;
	d->premisse[2] = b;
	tA = term_from_type (type_term (a->left));
	t_b = term_from_type (type_term (b->left));
	if (!equal_term (t_b, dt->right))
	{
	bad_type:
		sput ("\ndmKt: bad type\n", err);
		exit (-1);
	}
	if (dt->left->k != TERM_AP)
		goto bad_type;
	if (!equal_term (dt->left->ap.arg, a->left))
		goto bad_type;
	tB = dt->left->ap.fnc;
	d->left = ap (ap (ap (ap (Kt, tA), tB), a->left), b->left);
	d->right = a->right;
	return d;
}

/* #define DEM_St 's'	/* a:A->>\x(Bx->>Cx)=a', b:A->>B, c:A =>
				sABCabc = a'c'(b'c') */
dem dmSt (dem a, dem b, dem c)
{
dem d;
term tA, tB, tC;
type t, t_a, t_b, t_c;
term lx, x, r, Bx, Cx;
	ALLOC (d, *d);
	d->k = DEM_St;
	d->n_premisses = 3;
	d->premisse[0] = a;
	d->premisse[1] = b;
	d->premisse[2] = c;

	t_c = type_term (c->left);
	tA = term_from_type (t_c);
	t_b = type_term (b->left);
	if (t_b->k != TYPE_PFNC)
	{
	bad_type:
		sput ("\ndmSt: bad type\n", err);
		exit (-1);
	}
	if (!equal_type (t_b->fnc.arg, t_c))
		goto bad_type;
	tB = term_from_type (t_b->fnc.res);
	t_a = type_term (a->left);
	if (t_a->k != TYPE_PFNC)
		goto bad_type;
	if (!equal_type (t_a->pfnc.arg, t_c))
		goto bad_type;
	lx = t_a->pfnc.res;
	if (lx->k != TERM_ABST)
		goto bad_type;
	x = lx->abst.arg;
	r = lx->abst.res;
	if (r->k != TERM_AP)
		goto bad_type;
	if (r->ap.fnc->k != TERM_AP)
		goto bad_type;
	if (r->ap.fnc->ap.fnc->k != TYPE_PFNC)
		goto bad_type;
	Bx = r->ap.fnc->ap.arg;
	Cx = r->ap.arg;
	if (Bx->k != TERM_AP)
		goto bad_type;
	if (!equal_term (Bx->ap.arg, x))
		goto bad_type;
	tB = Bx->ap.fnc;
	if (Cx->k != TERM_AP)
		goto bad_type;
	if (!equal_term (Cx->ap.arg, x))
		goto bad_type;
	tC = Cx->ap.fnc;

	d->left = ap (ap (ap (ap (ap (ap (St, tA), tB), tC),
			a->left), b->left), c->left);
	d->right = ap (ap (a->right, c->right),
			ap (b->right, c->right));
	return d;
}

/* #define DEM_Yt 'y'	/* f:A->A=f' => yAf = f(yAf) */
dem dmYt (dem f)
{
dem d;
term tA;
type t_f;

	ALLOC (d, *d);
	d->k = DEM_Yt;
	d->n_premisses = 1;
	d->premisse[0] = f;

	t_f = type_term (f->left);
	if (t_f->k != TYPE_FNC)
	{
	bad_type:
		sput ("\ndmYt: bad type\n", err);
		exit (-1);
	}
	if (!equal_type (t_f->fnc.arg, t_f->fnc.res))
		goto bad_type;
	tA = term_from_type (t_f->fnc.res);

	d->left = ap (ap (Yt, tA), f->left);
	d->right = ap (f->right, d->left);
	/*ap (ap (Yt, tA), f->right));*/

	return d;
}

/* #define DEM_REP0 'Z'    /* f:A->A=f', x:A=x' => R[A]0fx=x' */
dem dmrep0 (dem f, dem x)
{
dem d;
type tA;
type tf;
	ALLOC (d, *d);
	d->k = DEM_REP0;
	d->n_premisses = 2;
	d->premisse[0] = f;
	d->premisse[1] = x;

	tf = type_term (f->left);
	if (tf->k != TYPE_FNC)
	{
	bad_type:
		sput ("\ndmrep0: bad type\n", err);
		exit (-1);
	}
	if (!equal_type (tf->fnc.arg, tf->fnc.res))
		goto bad_type;
	tA = type_term (x->left);
	if (!equal_type (tf->fnc.arg, tA))
		goto bad_type;

	d->left = ap (ap (ap (rep(tA), ZERO), f->left), x->left);
	d->right = x->right;
	return d;
}

/* #define DEM_REPEX '['	/* f:A->A=f' x:A=x' n:O=n' =>
				R[A](suc n)fx = f(R[A]nfx) */
dem dmrepex (dem f, dem x, dem n)
{
dem d;
type tA;
type tf;
	ALLOC (d, *d);
	d->k = DEM_REP0;
	d->n_premisses = 2;
	d->premisse[0] = f;
	d->premisse[1] = x;
	d->premisse[2] = n;

	tf = type_term (f->left);
	if (tf->k != TYPE_FNC)
	{
	bad_type:
		sput ("\ndmrep0: bad type\n", err);
		exit (-1);
	}
	if (!equal_type (tf->fnc.arg, tf->fnc.res))
		goto bad_type;
	tA = type_term (x->left);
	if (!equal_type (tf->fnc.arg, tA))
		goto bad_type;

	d->left = ap (ap (ap (rep(tA), ap (SUC, n->left)), f->left), x->left);
	d->right = ap (f->right, ap (ap (ap (rep(tA),
		n->right), f->right), x->right));
	return d;
}

/* #define DEM_REPIN ']'	/*			(ou R[A]nf(fx) ?) */
dem dmrepin (dem f, dem x, dem n)
{
dem d;
type tA;
type tf;
	ALLOC (d, *d);
	d->k = DEM_REP0;
	d->n_premisses = 2;
	d->premisse[0] = f;
	d->premisse[1] = x;
	d->premisse[2] = n;

	tf = type_term (f->left);
	if (tf->k != TYPE_FNC)
	{
	bad_type:
		sput ("\ndmrep0: bad type\n", err);
		exit (-1);
	}
	if (!equal_type (tf->fnc.arg, tf->fnc.res))
		goto bad_type;
	tA = type_term (x->left);
	if (!equal_type (tf->fnc.arg, tA))
		goto bad_type;

	d->left = ap (ap (ap (rep(tA), ap (SUC, n->left)), f->left), x->left);
	d->right = ap (ap (ap (rep(tA), n->right), f->right),
		ap (f->right, x->right));
	return d;
}

/* #define DEM_REPt0 'z'	/* f:A->A=f' x:A=x' => rAofx = x' */
dem dmrept0 (dem f, dem x)
{
dem d;
type tA, t_f, t_x;
	ALLOC (d, *d);
	d->k = DEM_REPt0;
	d->n_premisses = 2;
	d->premisse[0] = f;
	d->premisse[1] = x;

	t_f = type_term (f->left);
	t_x = type_term (x->left);
	if (t_f->k != TYPE_FNC)
	{
	bad_type:
		sput ("\ndmrept0: bad type\n", err);
		exit (-1);
	}
	if (!equal_type (t_f->fnc.arg, t_x))
		goto bad_type;
	if (!equal_type (t_f->fnc.res, t_x))
		goto bad_type;
	tA = t_x;
	d->left = ap (ap (ap (ap (REPt, term_from_type(tA)),
			ZERO), f->left), x->left);
	d->right = x->right;
	return d;
}

/* #define DEM_REPtEX '>'	/* f:A->A=f' x:A=x' n:O=n' =>
				rA(suc c)fx = f(rAnfx) */
dem dmreptex (dem f, dem x, dem n)
{
dem d;
type t_f, t_x, t_n, tA;

	ALLOC (d, *d);
	d->n_premisses = 3;
	d->premisse[0] = f;
	d->premisse[1] = x;
	d->premisse[2] = n;

	t_f = type_term (f->left);
	t_x = type_term (x->left);
	t_n = type_term (n->left);
	if (t_f->k != TYPE_FNC)
	{
	bad_type:
		sput ("\ndmrept0: bad type\n", err);
		exit (-1);
	}
	if (!equal_type (t_f->fnc.arg, t_x))
		goto bad_type;
	if (!equal_type (t_f->fnc.res, t_x))
		goto bad_type;
	if (!equal_type (t_n, ORD))
		goto bad_type;
	tA = t_x;

	d->left = ap (ap (ap (ap (REPt, term_from_type(tA)),
			ap (SUC, n->left)), f->left), x->left);
	d->right = ap (f->right,
		ap (ap (ap (ap (REPt, term_from_type (tA)),
			n->right), f->right), x->right));
	return d;
}

/* #define DEM_REPtIN '<'	/*			(ou rAnf(fx) ? */
dem dmreptIN (dem f, dem x, dem n)
{
dem d;
type t_f, t_x, t_n, tA;

	ALLOC (d, *d);
	d->n_premisses = 3;
	d->premisse[0] = f;
	d->premisse[1] = x;
	d->premisse[2] = n;

	t_f = type_term (f->left);
	t_x = type_term (x->left);
	t_n = type_term (n->left);
	if (t_f->k != TYPE_FNC)
	{
	bad_type:
		sput ("\ndmrept0: bad type\n", err);
		exit (-1);
	}
	if (!equal_type (t_f->fnc.arg, t_x))
		goto bad_type;
	if (!equal_type (t_f->fnc.res, t_x))
		goto bad_type;
	if (!equal_type (t_n, ORD))
		goto bad_type;
	tA = t_x;

	d->left = ap (ap (ap (ap (REPt, term_from_type(tA)),
			ap (SUC, n->left)), f->left), x->left);
	d->right = ap (ap (ap (ap (REPt, term_from_type (tA)),
			n->right), f->right), ap (f->right, x->right));
	return d;
}

/* #define DEM_TEST0 '0'	/* z:A0=z' s:O->>\n:A(n+1) => ?A0zs = z' */
dem dmtest0 (dem z, dem s)
{
dem d;
term tz, tA;
	ALLOC (d, *d);
	d->k = DEM_TEST0;
	d->n_premisses = 2;
	d->premisse[0] = z;
	d->premisse[1] = s;


	tz = term_from_type (type_term (z->left));
	if (tz->k != TERM_AP)
	{
	bad_type:
		sput ("\ndmtest0: bad type\n", err);
		exit (-1);
	}
	if (!equal_term (tz->ap.arg, ZERO))
		goto bad_type;
	tA = tz->ap.fnc;
	d->left = ap (ap (ap (ap (TEST, tA), ZERO), z->left), s->left);
	d->right = z->right;
	return d;
}

/* #define DEM_TEST1 '1'   /* z:A0=z' s:O->>\n:A(n+1) n:O=n' =>
				?(suc n)zs = sn */
dem dmtest1 (dem z, dem s, dem n)
{
dem d;
type t;
term t1, t2, t3;
term tA;
	ALLOC (d, *d);
	d->k = DEM_TEST0;
	d->n_premisses = 2;
	d->premisse[0] = z;
	d->premisse[1] = s;

	t = type_term (s->left);
	if (t->k != TYPE_PFNC)
	{
	bad_type:
		sput ("\ndmtest1: bad type\n", err);
		exit (-1);
	}
	t1 = t->pfnc.res;
	if (t1->k != TERM_ABST)
		goto bad_type;
	t2 = t1->abst.res;
	if (t2->k != TERM_AP)
		goto bad_type;
	t3 = t2->ap.arg;
	if (t3->k != TERM_AP)
		goto bad_type;
	if (!equal_term (t3->ap.fnc, SUC))
		goto bad_type;
	if (!equal_term (t3->ap.arg, t1->abst.arg))
		goto bad_type;
	tA = t2->ap.fnc;

	d->left = ap (ap (ap (ap (TEST, tA), ap (SUC, n->left)),
		z->left), s->left);
	d->right = ap (s->right, n->right);
	return d;

}

dem dmabst (dem a, dem r)
{
dem d;
	ALLOC (d, *d);
	d->k = DEM_ABST;
	d->n_premisses = 2;
	d->premisse[0] = a;
	d->premisse[1] = r;

	d->left = abst (a->left, r->left);
	d->right = abst (a->right, r->right);
	return d;
}

#define print_term write_term
#define print_type write_type

#define print_dem write_dem

/* #define DEM_LAMBDA '\\' /* x:A=x' y:B=y' z:A=z' => (\x.y)z = subst(x',y',z') */
dem dmsubst (dem d1, dem d2, dem d3)
{
dem d;
	sput ("\nd1 = ", trc); print_dem (d1, trc, 1);
	sput ("\nd2 = ", trc); print_dem (d2, trc, 1);
	sput ("\nd3 = ", trc); print_dem (d3, trc, 1);

	ALLOC (d, *d);
	d->k = DEM_SUBST;
	d->n_premisses = 3;
	d->premisse[0] = d1;
	d->premisse[1] = d2;
	d->premisse[2] = d3;
	d->left = ap (lambda (d1->left, d2->left), d3->left);
	sput ("\nd->left = ", trc); print_term (d->left, trc);
	d->right = subst (d1->right, d2->right, d3->right);
	sput ("\nd->right = ", trc); print_term (d->right, trc);
	sput ("\nd = ", trc); print_dem (d, trc, 1);
	return d;
}
/* a:t = a':t' t':T = t'':T => a:t = a':t'' */
dem dmeqtype (dem a, dem t)
{
dem d;
term t1;
	ALLOC (d, *d);
	d->k = DEM_EQTYPE;
	d->n_premisses = 2;
	d->premisse[0] = a;
	d->premisse[1] = t;

	t1 = term_from_type (type_term (a->right));
	if (!equal_term (t1, t->left))
	{
	bad_type:
		sput ("\ndmeqtype: bad type\n", err);
		exit (-1);
	}

	d->left = a->left;
	ALLOC (d->right, *(d->right));
	memcpy (d->right, a->right, sizeof(d->right));
	d->right->term.typ = type_from_term (t->right);
	return d;
}

dem constr (term t)
{
char buf[1000];
	switch (t->k)
	{
		case TERM_AP :
			return dmap (constr(t->ap.fnc), constr(t->ap.arg));
		case TERM_ABST :
			return dmabst (constr(t->abst.arg),
				constr(t->abst.res));
		case TERM_VAR :
			return EX_var (t->var.name, t->var.typ);
		case TERM_I :
			return EX_I (t->I.a);
		case TERM_K :
			return EX_K (t->K.a, t->K.b);
		case TERM_S :
			return EX_S (t->S.a, t->S.b, t->S.c);
		case TERM_Y :
			return EX_Y (t->Y.a);
		case TERM_ZERO :
			return EX_ZERO;
		case TERM_SUC :
			return EX_SUC;
		case TERM_LIM :
			return EX_LIM;
		case TERM_REP :
			return EX_rep (t->rep.a);
/* #define TERM_UNDEF 'U' */
 /* It t = I[t] */
		case TERM_It :
			return EX_It;
		case TERM_Kt :
			return EX_Kt;

#define TERM_St 's'
		case TERM_St :
			return EX_St;

#define TERM_Yt 'y'
		case TERM_Yt :
			return EX_Yt;
		case TERM_TEST :
			return EX_TEST;
#define TERM_TEST '?'
#define TERM_REPt 'r'

		case TERM_REPt :
			return EX_REPt;

	/*T_ORD->k = TYPE_ORD; T_ORD->term.typ = TYPE;*/
		case TYPE_ORD :
			return EX_ORD;
	/*T_UNDEF->k = TYPE_UNDEF; T_UNDEF->term.typ = TYPE;*/
		case TYPE_UNDEF :
			return EX_UNDEF;
	/*T_TYPE->k = TYPE_TYPE; T_TYPE->term.typ = TYPE;*/
		case TYPE_TYPE :
			return EX_TYPE;
	/*T_FNC->k = TYPE_FNC; T_FNC->term.typ = fnc (TYPE, fnc (TYPE, TYPE));*/
		case TYPE_FNC :
			return EX_FNC;
	/*T_PFNC->k = TYPE_PFNC; T_PFNC->term.typ = calcul_type_term (T_PFNC);*/
		case TYPE_PFNC :
			return EX_PFNC;
	/*trace_term (T_PFNC);*/
		default:
			sprintf (buf, "\nUnknown term 0x%X\n", t->k);
			exit (-1);


	}

}

#define lim(x) ap(LIM,x)
#define rpt(t,n,f,x) ap (ap (ap (rep(t), n), f), x)

#define rtxf(t,x,f) lambda (nrtxf, ap (ap (ap (rep(t), nrtxf), f), x))

main ()
{
term x, n, nrtxf;
type t;
term plus_omega, omega_2, plus_omega_2, plus_omega_n, omega_n, omega_omega,
	plus_omega_omega;
term f, p, q, r, g;
term ford, limford, limford1, omega_suc, psi, phi, plus_epsilon_0, epsilon_0;
type tlimford;
term z, s, n1;
term tmp[50];
dem d, td[40];

	param_out.fd = stdout;
	param_err.fd = stderr;
	param_trc.fd = stderr;
	init ();
	/* Exemple : construction de l'ordinal omega * 2 */
	x = ap (LIM, ap (ap (S(ORD,ORD,ORD),
		ap (ap (S(ORD,fnc(ORD,ORD),fnc(ORD,ORD)),rep(ORD)),
			ap(K(fnc(ORD,ORD),ORD),SUC))),
		ap(K(ORD,ORD),ap(LIM,I(ORD)))));
	sput ("x = ", out);
	write_term (x, out);
	t = type_term (x);
	sput ("\nt = ", out);
	write_type (t, out);
	sput ("\n", out);
#if 0
	n = var ("n", ORD);
	/*
	x = ap (LIM, lambda (n,
		ap (ap (ap (rep(ORD), n), SUC), ap (LIM, I(ORD)))
			));
		*/
	x = ap (ap (ap (rep(ORD), n), SUC), ap (LIM, I(ORD)));
	/*   x = ap (rep(ORD), n); */

	sput ("x = ", out);
	write_term (x, out);
	t = type_term (x);
	sput ("\nt = ", out);
	write_type (t, out);
	sput ("\n", out);

	x = lambda (n, x);
	sput ("x = ", out);
	write_term (x, out);
	t = type_term (x);
	sput ("\nt = ", out);
	write_type (t, out);
	sput ("\n", out);

	x = ap (LIM, x);
	sput ("x = ", out);
	write_term (x, out);
	t = type_term (x);
	sput ("\nt = ", out);
	write_type (t, out);
	sput ("\n", out);

	x = var ("x", ORD);
	plus_omega = lambda (x, lim (lambda (n,
		rpt (ORD, n, SUC, x)
			)));
	omega_2 = lim (lambda (n, rpt (ORD, n, plus_omega, ZERO)));
	t = type_term (omega_2);
	sput ("Type of omega_2 = ", out);
	write_type (t, out);
	sput ("\n", out);

	plus_omega_2 = lambda (x, lim (lambda (n,
		rpt (ORD, n, plus_omega, x))));
	t = type_term (plus_omega_2);
	sput ("Type of plus_omega_2 is ", out);
	write_type (t, out);

	f = var ("f", fnc(ORD,ORD));
	p = var ("p", ORD);

	plus_omega_n = lambda (n, rpt (fnc(ORD,ORD), n, lambda (f,
		lambda (x, lim (lambda (p, rpt (ORD, p, f, x)))) ),
		SUC));
	/*
	next_power = lambda (f,
		lambda (x, lim (lambda (p, rpt (ORD, p, f, x)))));
	plus_omega_n = lambda (n, rpt (fnc(ORD,ORD), n,
	*/
	t = type_term (plus_omega_n);
	sput ("\nType of plus_omega_n is ", out);
	write_type (t, out);

	omega_n = lambda (n, ap (ap (plus_omega_n, n), ZERO));
	t = type_term (omega_n);
	sput ("\nType of omega_n is ", out);
	write_type (t, out);

	omega_omega = lim (omega_n);
	t = type_term (omega_omega);
	sput ("\nType of omega_omega is ", out);
	write_type (t, out);

	plus_omega_omega = lambda (x, lim (lambda (n,
					    ap (ap (plus_omega_n, n), x) )));
	t = type_term (plus_omega_omega);
	sput ("\nType of plus_omega_omega is ", out);
	write_type (t, out);
#endif
/*
	Construction de epsilon 0 :
	ford 0 = O
	ford 1 = O->O...
	ford n = test (K[T,O] T) n O (\p. F (ford p) (ford p))
	ford = Y [O->T] \ford \n
		test (K[T,O] T) n O (\p. F (ford p) (ford p))
*/
	f = var ("f", fnc(ORD,TYPE));
	n = var ("n", ORD);
	p = var ("p", ORD);
	nrtxf = var ("nrtxf", ORD);
	/*
	ford = ap (Y(fnc(ORD,TYPE)), lambda (f, lambda (n,
		ap (ap (ap (ap (TEST, ap (K(TYPE,ORD), TYPE)), n), T_ORD),
			lambda (p, ap (ap (T_FNC, ap (f, p)), ap (f, p)))
			) )));
	*/

	tmp[1] = Y(fnc(ORD,TYPE)); trace_term (tmp[1]);
	tmp[2] = ap (K(TYPE,ORD), T_TYPE); trace_term (tmp[2]);
	tmp[3] = ap (TEST, tmp[2]); trace_term (tmp[3]);
	tmp[4] = ap (tmp[3], n); trace_term (tmp[4]);
	tmp[5] = ap (tmp[4], T_ORD); trace_term (tmp[5]);
	tmp[6] = ap (f, p); trace_term (tmp[6]);
	tmp[7] = ap (T_FNC, tmp[6]); trace_term (tmp[6]);
	tmp[8] = ap (tmp[7], tmp[6]); trace_term (tmp[8]);
	tmp[9] = lambda (p, tmp[8]); trace_term (tmp[9]);
	tmp[10] = ap (tmp[5], tmp[9]); trace_term (tmp[10]);
	tmp[11] = lambda (n, tmp[10]); trace_term (tmp[11]);
	tmp[12] = lambda (f, tmp[11]); trace_term (tmp[12]);
	ford = ap (tmp[1], tmp[12]); trace_term (ford);

	t = type_term (ford);
	sput ("\nType of ford is ", out);
	write_type (t, out);

/*
	limford 0 = lim
	limford (n+1) f:O->ford(n+1) g:ford n = limford n (\p.f p g)

	tlimford = pfnc (ORD, lambda (q, fnc (fnc (ORD, ap (ford, q)),
						ap (ford, q) )));
*/
	q = var ("q", ORD);
	r = var ("r", ORD);
	n1 = var ("n1", ORD);
	f = var ("f", fnc (ORD, type_from_term (ap (ford, ap (SUC, n1)))));
	g = var ("g", type_from_term (ap (ford, n1)));

	tlimford = pfnc (ORD, lambda (q, ap (ap (T_FNC,
		ap (ap (T_FNC, T_ORD), ap (ford, q)) ),
			ap (ford, q) )));
	limford1 = var ("limford1", tlimford);

	sput ("\ntlimford = ", out);
	write_type (tlimford, out);

/*
	limford = ap (Y(tlimford), lambda (limford1,
		lambda (n, ap (ap (ap (ap (TEST,
		  lambda (r, fnc (fnc (ORD, ap (ford, r)), ap (ford, r))) ),
		    n), LIM),
			lambda (n1, lambda (f, lambda (g,
				ap (ap (limford1, n),
					lambda (p, ap (ap (f, p), g))
					) ))) )) ));
*/
	f = var ("f", fnc (ORD, TYPE));
	td[1] = constr (tmp[12]/*ford*/);
	td[2] = dmY (td[1]); /* YF = F(YF) */
	td[3] = constr (f);
	td[4] = constr (tmp[11]);
	td[23] = constr (ford);
	sput ("\ntd[3] = ", trc);
	print_dem (td[3], trc, 1);
	sput ("\ntd[4] = ", trc);
	print_dem (td[4], trc, 1);
	sput ("\ntd[23] = ", trc);
	print_dem (td[23], trc, 1);
	sput ("\n", trc);
	td[5] = dmsubst (td[3], td[4], td[23]);
	sput ("\ntd[5] = ", trc);
	print_dem (td[5], trc, 1);
	td[6] = dmtrans (td[2], td[5]);
	td[7] = constr (ap (SUC, n));
	td[8] = dmap (td[6], td[7]);
	td[9] = constr (n);
	td[10] = constr (td[5]->right->abst.res);
	td[11] = dmsubst (td[9], td[10], td[7]);
	td[12] = dmtrans (td[8], td[11]);
	td[13] = constr (ap (K(TYPE,ORD), T_TYPE));
	td[14] = constr (T_ORD);
	td[15] = constr (lambda (p, ap (ford, p)));
	td[16] = dmtest1 (/*td[13],*/ td[14], td[15], td[9]);
	td[17] = dmtrans (td[12], td[16]);
	td[18] = constr (p);
	td[19] = constr (ap (ap (T_FNC, ap (ford, p)), ap (ford, p)));
	td[20] = dmsubst (td[18], td[19], td[9]);
	td[21] = dmtrans (td[17], td[20]);
	d = td[21];

	limford = ap (Y(tlimford), lambda (limford1,
		lambda (n, ap (ap (ap (ap (TEST,
		  lambda (r, ap (ap (T_FNC,
				ap (ap (T_FNC, T_ORD), ap (ford, r)) ),
					ap (ford, r) )) ),
		    n), LIM),
			lambda (n1, lambda (f, lambda (g,
				ap (ap (limford1, n),
					lambda (p, apt (d, ap (f, p), g))
					) ))) )) ));

	sput ("\nlimford = ", out);
	write_term (limford, out);
	sput ("\nhas type ", out);
	write_type (type_term (limford), out);

/*
	omega_suc 0 = \f:O->O. \x:O. lim (rep[O] x f)
	omega_suc 1 = \f:(ford 2). \x:(ford 1). lim (rep[ford 1] x f)

	omega_suc = \n:O. \f:(ford (suc n)). \x:(ford n).
			lim (rep[ford n] x f)
*/
	f = var ("f", type_from_term (ap (ford, ap (SUC, n))));
	x = var ("x", type_from_term (ap (ford, n)));
	/*
	omega_suc = lambda (n, plambda (f, plambda (x,
		ap (LIM, rtxf (type_from_term (ap (ford, n)), x, f)) )));
	*/
	omega_suc = lambda (n, plambda (f, plambda (x,
		ap (ap (limford, n),
			lambda (p, ap (ap (ap (ap (REPt, ap (ford, n)),
				p), f), x)) ) )));

	t = type_term (omega_suc);
	sput ("\nType of omega_suc is ", out);
	write_type (t, out);
/*
	psi n p = test n (\z:(ford p).\s:(ford:suc p).It(ford p))
			(\n1:O.\z:(ford p).\s:(ford:suc p).
			psi n1 (suc p) s (omega_suc p) s)

	psi = Y[O->O->O->(O->O)->O->O] (\psi.\n.\p.
		test n (\z:(ford p). \s:(ford:suc p). It(ford p))
			(\n1:O. \z:(ford p). \s:(ford:suc p).
			psi n1 (suc p) s (omega_suc p) s))
*/
	z = var ("z", type_from_term (ap (ford, p)));
	s = var ("s", type_from_term (ap (ford, ap (SUC, p))));
	n1 = var ("n1", ORD);

	psi = ap (Y (fnc (ORD, fnc (ORD, fnc (ORD, fnc (fnc(ORD,ORD),
			fnc (ORD, ORD) ))))),
		lambda (f, plambda (n, plambda (p,
			ap (ap (ap (ap (TEST,
				ap (K(TYPE,ORD),
					term_from_type
					    (fnc(ORD,fnc(fnc(ORD,ORD),
						fnc(ORD,ORD) )) ) )
						), n),
			    plambda (z, plambda (s, ap (It, ap (ford, p)))) ),
				plambda (n1, plambda (z, plambda (s,
					ap (ap (ap (ap (ap (f, n1),
					    ap (SUC, p)),
						s),
						    ap (omega_suc, p)),
							s) ))) ) ))) );
	t = type_term (psi);
	sput ("\nType of psi is ", out);
	write_type (t, out);
/*
	phi n = psi n 0
	+epsilon0 = \x.lim (\n.phi n 0 suc x)
	epsilon0 = lim (\n. phi n 0 suc 0)
*/
	phi = lambda (n, ap (ap (psi, n), ZERO));
	t = type_term (phi);
	sput ("\nType of phi is ", out);
	write_type (t, out);

	x = var ("x", ORD);
	plus_epsilon_0 = lambda (x, ap (LIM, lambda (n,
		ap (ap (ap (ap (phi, n), ZERO), SUC), x) )));
	t = type_term (plus_epsilon_0);
	sput ("\nType of plus_epsilon_0 is ", out);
	write_type (t, out);

	epsilon_0 = ap (LIM, lambda (n,
		ap (ap (ap (ap (phi, n), ZERO), SUC), ZERO) ));
	t = type_term (epsilon_0);
	sput ("\nType of epsilon_zero is ", out);
	write_type (t, out);

	sput ("\n", out);


}
