
/* #define TRACE */

#include <stdio.h>
#include <errno.h>
#include <stdlib.h>

#include "stream.h"

/*
struct param_file param_out = { stdout },
		  param_err = { stderr };
*/
struct param_file param_out, param_err;

struct put_fnct out[1] = { f_put_file, &param_out },
		err[1] = { f_put_file, &param_err };

#define TYPE_ORD 'O'
#define TYPE_UNDEF 'U'
#define TYPE_FNC 'F'

union u_type
{
	char k;
	struct type_fnc
	{
		char k;
		union u_type *arg;
		union u_type *res;
	} fnc;
};

typedef union u_type *type;

union u_type ORD[1], UNDEF[1];

#define TERM_I 'I'
#define TERM_K 'K'
#define TERM_S 'S'
#define TERM_Y 'Y'
#define TERM_ZERO '0'
#define TERM_SUC '\''
#define TERM_LIM 'L'
#define TERM_REP 'r'
#define TERM_AP '-'
#define TERM_VAR 'V'
#define TERM_UNDEF 'U'

union u_term
{
	char k;
	struct term_I
	{
		char k;
		type a;
	} I;
	struct term_K
	{
		char k;
		type a, b;
	} K;
	struct term_S
	{
		char k;
		type a, b, c;
	} S;
	struct term_Y
	{
		char k;
		type a;
	} Y;
	struct term_rep
	{
		char k;
		type a;
	} rep;
	struct term_ap
	{
		char k;
		union u_term *fnc, *arg;
	} ap;
	struct term_var
	{
		char k;
		char *name;
		type typ;
	} var;
};

typedef union u_term *term;

union u_term ZERO[1], SUC[1], LIM[1], UNDEF_TERM[1];

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

init ()
{
/*
	out->f = f_put_file;
	out->p = param_out;

	err->f = f_put_file;
	err->p = param_err;
*/
	ORD->k = TYPE_ORD;
	UNDEF->k = TYPE_UNDEF;

	ZERO->k = TERM_ZERO;
	SUC->k = TERM_SUC;
	LIM->k = TERM_LIM;
	UNDEF_TERM->k = TERM_UNDEF;

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

term I (type a)
{
term i;
	ALLOC (i, struct term_I);
	i->k = TERM_I;
	i->I.a = a;
	return i;
}

term K (type a, type b)
{
term k;
	ALLOC (k, struct term_K);
	k->k = TERM_K;
	k->K.a = a;
	k->K.b = b;
	return k;
}

term S (type a, type b, type c)
{
term s;
	ALLOC (s, struct term_S);
	s->k = TERM_S;
	s->S.a = a;
	s->S.b = b;
	s->S.c = c;
	return s;
}

term Y (type a)
{
term y;
	ALLOC (y, struct term_Y);
	y->k = TERM_Y;
	y->Y.a = a;
	return y;
}

term rep (type a)
{
term r;
	ALLOC (r, struct term_rep);
	r->k = TERM_REP;
	r->rep.a = a;
	return r;
}

term ap1 (term fnc, term arg)
{
term a;
	ALLOC (a, struct term_ap);
	a->k = TERM_AP;
	a->ap.fnc = fnc;
	a->ap.arg = arg;
	return a;
}

int equal_type (type a, type b)
{
	if (a->k != b->k)
		return 0;
	if (a->k != TYPE_FNC)
		return 1;
	if (!equal_type (a->fnc.arg, b->fnc.arg))
		return 0;
	if (!equal_type (a->fnc.res, b->fnc.res))
		return 0;
	return 1;
}

term var (char *name, type t)
{
term v;
	ALLOC (v, struct term_var);
	v->k = TERM_VAR;
	v->var.name = name;
	v->var.typ = t;
	return v;
}

write_type (type t, struct put_fnct *put)
{
	switch (t->k)
	{
		case TYPE_ORD:
			sput ("O", put);
			break;
		case TYPE_FNC:
			if (t->fnc.arg->k == TYPE_FNC)
				sput ("(", put);
			write_type (t->fnc.arg, put);
			if (t->fnc.arg->k == TYPE_FNC)
				sput (")", put);
			sput ("->", put);
			write_type (t->fnc.res, put);
			break;
		default:
			sput ("?", put);
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
			sput (":", put);
			write_type (x->var.typ, put);
			sput ("> ", put);
			break;
		case TERM_UNDEF:
			sput (" U ", put);
			break;
		default:
			sput ("?", put);

	}
}

type type_term (term x);

type type_term_1 (term x)
{
	switch (x->k)
	{
		case TERM_I: 	/* a->a */
			return fnc (x->I.a, x->I.a);
		case TERM_K:    /* a->(b->a) */
			return fnc (x->K.a, fnc (x->K.b, x->K.a));
		case TERM_S:	/* (a->b->c) -> (a->b) -> a -> c */
			return fnc (fnc (x->S.a, fnc (x->S.b, x->S.c)),
				fnc (fnc (x->S.a, x->S.b),
					fnc (x->S.a, x->S.c)));
		case TERM_Y:
			return fnc (fnc (x->Y.a, x->Y.a), x->Y.a);
		case TERM_ZERO:
			return ORD;
		case TERM_SUC:
			return fnc (ORD, ORD);
		case TERM_LIM:
			return fnc (fnc (ORD, ORD), ORD);
		case TERM_REP:
			return fnc (ORD, fnc (fnc (x->rep.a, x->rep.a),
						fnc (x->rep.a, x->rep.a)));
		case TERM_AP:
		{
		type tf;
			tf = type_term (x->ap.fnc);
			if (tf->k != TYPE_FNC)
			{
				sput ("type_term: invalid function\n", err);
				return UNDEF;
			}
			return tf->fnc.res;
		}
		case TERM_VAR:
			return x->var.typ;
		default:
			return UNDEF;
	}
}

type type_term (term x)
{
type t;
#ifdef TRACE
	sput ("Type of ", err);
	write_term (x, err);
	sput ("...\n", err);
#endif
	t = type_term_1 (x);
#ifdef TRACE
	sput ("type of ", err);
	write_term (x, err);
	sput ("is ", err);
	write_type (t, err);
	sput (".\n", err);
#endif
	return t;
}

term ap (term fnc, term arg)
{
type tf, ta;
	tf = type_term (fnc);
	if (tf->k != TYPE_FNC)
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
	return ap1 (fnc, arg);
}

int occur (term v, term x)
{
	if (x->k == TERM_VAR && !strcmp (x->var.name, v->var.name) &&
		equal_type (x->var.typ, v->var.typ))
		return 1;
	if (x->k != TERM_AP)
		return 0;
	if (occur (v, x->ap.fnc))
		return 1;
	if (occur (v, x->ap.arg))
		return 1;
	return 0;
}

term lambda (term v, term x);

term lambda_1 (term v, term x)
{
term f, a;
type tf;
	if (v->k != TERM_VAR)
	{
		sput ("lambda: 1st arg not variable\n", err);
		return UNDEF_TERM;
	}
	if (x->k == TERM_VAR && !strcmp (x->var.name, v->var.name) &&
		equal_type (x->var.typ, v->var.typ))
		return I (v->var.typ);
	if (!occur (v, x))
		return ap (K (type_term (x), v->var.typ), x);
	f = x->ap.fnc;
	a = x->ap.arg;
	if (a->k == TERM_VAR && !strcmp (a->var.name, v->var.name) &&
		equal_type (a->var.typ, v->var.typ) &&
		!occur (v, f))
		return f;
	tf = type_term (f);
	return ap (ap (S (v->var.typ, type_term (a), tf->fnc.res),
			lambda (v, f)),
				lambda (v, a));
}

term lambda (term v, term x)
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

#define lim(x) ap(LIM,x)
#define rpt(t,n,f,x) ap (ap (ap (rep(t), n), f), x)

main ()
{
term x, n;
type t;
term plus_omega, omega_2, plus_omega_2, plus_omega_n, omega_n, omega_omega,
	plus_omega_omega;
term f, p;

	param_out.fd = stdout;
	param_err.fd = stderr;
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

	sput ("\n", out);

}

