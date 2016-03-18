
#include <stdio.h>
#include <errno.h>

#include "alloc.h"

#include "stream.h"

struct param_file param_out = { stdout },
		  param_err = { stderr },
		  param_trc = { stderr };

struct put_fnct out[1] = { f_put_file, &param_out },
		err[1] = { f_put_file, &param_err },
		trc[1] = { f_put_file, &param_trc };

/*

	termes :
		I[a], K[a,b], S[a,b,c], Y[a]
		It, Kt, St, Yt
			It a = I[a] ...
		0 suc lim
		test (rep) (rept)
		var
		undef
		lambda
		ap (abst)

	types:
		Ord
		Type
		Undef
		a -> b = FNC a b
		a ->> b = PFNC a b

	dem:
		(nom) a = b : regle premisses...

struct s_dem
{
	char k;
	term left, right;
	char *name;
	int n_premisses;
	struct s_dem *premisse[MAX_PREMISSES];
};
*/
/*
typedef struct s_dem *dem;

struct s_dem EX_ZERO[1], EX_SUC[1], EX_LIM[1], EX_UNDEF_TERM[1],
	EX_It[1], EX_Kt[1], EX_St[1], EX_Yt[1], EX_TEST[1], EX_REPt[1],
	EX_ORD[1], EX_UNDEF[1], EX_TYPE[1], EX_FNC[1], EX_PFNC[1];

type TYPE_It, TYPE_Kt, TYPE_St, TYPE_TFNC, TYPE_TPFNC, TYPE_REPt, TYPE_TEST;

	Representation unifiee :
		- types representes par termes
		- terme x representes par dem x = x

	structure unique : pointeur sur structure dem
	tableau de structures
	avant allouer chercher si existe deja

	elements de base : axiomes dem a = a, a atome
		undef lambdat var Yt
		0 suc lim test
		Type Ord Undef FNC PFNC
		variables

*/

#define TERM_UNDEF 'U'
#define TERM_LAMBDA '\\'
#define TERM_VAR 'V'
#define TERM_FIX 'Y'
#define TERM_ZERO '0'
#define TERM_SUC '\''
#define TERM_LIM 'l'
#define TERM_TEST '?'
#define TERM_TYPE 'T'
#define TERM_ORD 'O'
#define TERM_PFNC 'f'

/*
	constr termes : ap -> DEM_APt

	regles
		sym trans ap
		Yt
		test0 test1
		subst
		chtype

		changement de type :
			a=b:A
			A=B:T
			-> a=b:B

	point fixe :
		Yt A f = f (Yt A f)
			f: A->A
		sans typage :
		Y f = A (B f A) = (B f A) (B f A)
		    = (\h.hh) (\h.f(hh))
		    = (\h.f(hh)) (\h.f(hh))
		    = f ((\h.f(hh)) (\h.f(hh)))
		probleme avec typage : \h.hh impossible
		-> point fixe primitif

	\x:A.y:B = lambdat A B x y : A->B

#define DEM_It 'i'	 a:A=a' => iAa=a'

		1. a=b:A

		2. ax \=\
		3. type(1) A=A:T
		4. ap 2 3 => \A=\A
		5. ap 4 3 => \AA=\AA
		6. var x=x:A
		7. ap 5 6 => \AAx = \AAx
		8. ap 7 6 => \AAxx = \AAxx (=I[A] = It A)
		9. subst 6 6 1 => \AAxxa = subst(x,x,b) = b

		notation: \ABxy = \x:A.y:B (ou \AxBy ?)
		It = \A:T.(It A):A->A = \A:T.(\x:A.x:A)A->A
			= \T(A->A)A(\AAxx)

		plambdat
		^AxBy = \x:A.y:Bx  A:T B:A->T

		f = \ABxy : A->B	x:A |-> fx = y: B
		f = ^AxBy : A->>B	x:A |-> fx = y: Bx
			A:T x:A B:A->T y:Bx

		It = ^TA (\A.A->A)(^Ax (KA)x)
		It = ^TA (\A.A->A)(^Ax (^Ax TA)x)
		It = ^TA (^TA (^TA TT)(fA(KA)))(^Ax (^Ax TA)x)
		It = ^TA (^TA (^TA TT)(fA(^Ax (^Ax (^Ax TT)T)A)))(^Ax (^Ax (^Ax TT)A)x)
		faux
		It = ^TA (^TA T(fA(^Ax TA))) (^Ax (^Ax TA)x) faux
					     I[a] = It a
		f = ^Ax By			f:A->>B, x:A => fx=y:Bx
		  = ^Ax (^Ax T(Bx))y faux	(B = (^Ax T(Bx))	y:Bx, Bx:T
		f = ^Ax (^Ax (^Ax TT)(Bx))y faux	(B = (^Ax (^Ax TT)(Bx))
		f = ^Ax (^Ax (^Ax (^Ax...
		f = ^Ax (^Ax KT(Bx))y	KT atome ?
		f = ^x:A.y:Bx

		f = L Ax (Bx)y = ^x:A.y:Bx
			A:T x:A Bx:T y:Bx
			f: A->>LAx T(Bx)

		It = ^A:t. (^x:A.x:A): f A (^x:A.A:T)
					   (^Ax (^Ax (^Ax TT)T)A)

		It = LTA (fA(LAxTA))(LAxAx)

		1. a=b:A
			=> It A a = b ?

		It A = LTA (fA(LAxTA))(LAxAx) A
		subst
		2.	(ax T=T:T)
		3.	type(1) A=A:T
		4.	constr LAxAx=LAxAx
		5. subst(3,4,3) => It A = subst(A,LAxAx,A)
				   It A = L Ax Ax
		6. ap 5 1 => It A a = L Ax Ax b
		subst
		7.	ax x=x:A
		8.	right(1) b=b
		9. subst(7,7,8) => L Ax Ax b = subst(x,x,b)
				   L Ax Ax b = b
		10. trans(6,9) => It A a = b

*/

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

#define MAX_PREMISSES 3
#define MAX_DEM 2000

struct s_dem 	/* dem a = b : t */
{
	struct s_dem *left, *right, *type; /* dem a = a, b = b, t = t */
	void *param;
	char regle, n_premisses;
	struct s_dem *premisse[MAX_PREMISSES];
};

typedef struct s_dem *dem;

int n_dem = 0;
struct s_dem tab_dem[MAX_DEM];


#define TERM_UNDEF 'U'
#define TERM_LAMBDA '\\'
#define TERM_VAR 'V'
#define TERM_FIX 'Y'
#define TERM_ZERO '0'
#define TERM_SUC '\''
#define TERM_LIM 'l'
#define TERM_TEST '?'
#define TERM_TYPE 'T'
#define TERM_ORD 'O'
#define TERM_PFNC 'f'

struct s_dem UNDEF[1], LAMBDA[1], FIX[1], ZERO[1], SUC[1], LIM[1], TEST[1],
	TYPE[1], ORD[1], PFNC[1];

#define DA(x,y) \
	x->left = x; \
	x->right = x; \
	x->regle = DEM_AXIOM; \
	x->n_premisses = 0;

init_nlct ()
{
	DA(LAMBDA)
	DA(FIX)
	DA(ZERO)
	DA(SUC)
	DA(LIM)
	DA(TEST)
	DA(TYPE)
	DA(ORD)
	DA(UNDEF)
	DA(PFNC)

	TYPE->type = TYPE;
	ORD->type = TYPE;
	UNDEF->type = TYPE;

	/* PFNC->type = ap (ap (PFNC, TYPE),
		PFNC = ^A:T.^B:A->T.A->>B:T
		PFNC: T->>\A.((A->T)->T)
			probleme: PFNC nec. pour def. son type
			ap1 non typee ou type resultat fourni
		PFNC A B
		     A:T B:A->T
		f:A->>B = PFNC A B
		x:A
		fx:Bx
		B:A->T

		A->B = A->>^x:A.B:tB avec tB = type de B

	TYPE_TPFNC = pfnc (TYPE, lambda (t,
				ap (ap (T_FNC,
					ap (ap (T_FNC, t), T_TYPE)
					), T_TYPE)
					  ));

	*/

	/*
	Yt->term.typ = pfnc (TYPE, lambda (t,
			ap (ap (T_FNC, ap (ap (T_FNC, t), t)), t) ));

	*/

	ZERO->type = ORD;
	SUC->type = ap (ap (PFNC, ORD), ORD);
	LIM->type = ap (ap (PFNC, ap (ap (PFNC, ORD), ORD)), ORD);
/* TEST
			r = pfnc (fnc(ORD,TYPE), lambda (a,
				ap (ap (T_PFNC, T_ORD), lambda (n,
				    ap (ap (T_FNC, ap (a, n)),
					ap (ap (T_FNC,
					    ap (ap (T_FNC, ORD), ap (a, n))
					       ), ap (a, n)) ) )) ));


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

*/

}

