
#include "lctm.h"

/* #define trace_dem(s,d) */

int atom (DEM d)
{
        /* trace_dem ("atom", d); */
	switch (node(d))
	{
		/*
		case _I:
		case _K:
		case _S:
		case _E:
		case _If:
		case _Ord:
			return 1;
		*/
		case _ap:
        /* case _DBLambda: */
		/*
		case transym:
		case _defI:
		case _defK:
		case _defS:
		*/
                        /* trace_dem ("atom=0", 0); */
			return 0;
		default:
                        /* trace_dem ("atom=1", 1); */
			return 1;
        }
}

DEM sym (DEM ab)
{
DEM aa, ba;
	aa = left (ab);
	ba = transym1 (ab, aa);
	return ba;
}

DEM trans (DEM ab, DEM bc)
{
DEM ba, ac;
	ba = sym (ab);
	ac = transym1 (ba, bc);
	return ac;
}

DEM used = NULL;

DEM red1 (DEM x, int red_arg);

DEM red (DEM x)
{
DEM r;
	r = red1 (x, 1);
/* #define TRACE */
        trace_dem ("red returns", r);
/* #undef TRACE */
	return r;
}

DEM red2 (DEM x, int red_arg);

DEM red1 (DEM x, int red_arg)
{
DEM d;
int i;
    if (red_arg != 0 && red_arg != 1)
        printf (" ERROR %d ", red_arg);
    for (i=0; i<nnr; i++)
    {
        /* printf ("i=%d\n", i); */
        trace_dem ("", no_red[i]);
        trace_dem ("", x);
        if (no_red[i] == x)
            return x;
    }
    if (used == NULL && x->_red[red_arg] != NULL)
        return x->_red[red_arg];
    else
    {
        d = red2 (x, red_arg);
        trace_dem ("red1 returns", d);
        if (used == NULL)
        	x->_red[red_arg] = d;
        return d;
    }
}

DEM red3 (DEM x, int red_arg);

DEM red2 (DEM x, int red_arg)
{
DEM t1, t2, t3;
int i;
    t1 = red3 (x, red_arg);
    for (;;)
    {
        for (i=0; i<nnr; i++)
        {
            /* printf ("i=%d\n", i); */
            trace_dem ("", no_red[i]);
            trace_dem ("", right(t1));
            if (no_red[i] == right(t1))
                return t1;
        }
        t2 = red3 (right(t1), red_arg);
        if (left(t2) == right(t2))
                return t1;
        t1 = trans (t1, t2);
    }
}

DEM red3 (DEM x, int red_arg)
{
DEM t, t1, t2, t3, t4, t5;
int i;
/*
{
char format[1000];
        printf ("trace_dem %s %x\n", "red1", x);
        sprintf (format, "%s(%d) %s : %s = ", __FILE__, __LINE__, "red1", "x");
        print_string (print_param, format);
        print_dem (print_param, x);
        print_string (print_param, "\n");
}
*/
/* #define trace_dem(s,d) \
{ \
char format[1000]; \
        sprintf (format, "%s(%d) %s : %s = ", __FILE__, __LINE__, s, #d); \
        print_string (print_param, format); \
        print_dem (print_param, d); \
        print_string (print_param, "\n"); \
}
*/
/*        { extern int flag_trace; if (flag_trace) printf (" test "); } */
        trace_dem ("red1", x);
        for (i=0; i<nnr; i++)
        {
            /* printf ("i=%d\n", i); */
            trace_dem ("", no_red[i]);
            trace_dem ("", x);
            if (no_red[i] == x)
                return x;
        }
	/*if (atom(x))
		return x;*/

        if (used != NULL && x == left(used))
            return used;
#if 1
        if ((flags & FLAG_RED_LAMBDA) && node(x) == _DBLambda)
        {
            /* return DBLambda (red1 (subdem(0,x), red_arg)); */
            t1 = red1 (subdem(0,x), red_arg);
            trace_dem ("DBLambda", t1);
            t2 = DBLambda (t1);
            trace_dem ("DBLambda", t2);
            return t2;
        }
#endif
        if (atom(x))
            return x;
        if (node(fnc(x)) == _Lambda || node(fnc(x)) == _Ext)
        {
            return Subst (subdem(0,fnc(x)), subdem(1,fnc(x)), arg(x));
        }
        if (node(fnc(x)) == _DBLambda)
        {
#if 1
            return DB_Subst (subdem(0,fnc(x)), arg(x));
#else
            t1 = red1 (subdem(0,fnc(x)), red_arg);
            if (red_arg)
               t2 = red1 (arg(x), red_arg);
            else
               t2 = arg(x);
            t3 = DB_Subst (t1, t2);
            return t3;
#endif
        }
        if (fnc(x) == I)
	{
                /* if (red_arg) */
                    t1 = red1 (arg(x), red_arg);
                /* else
                    t1 = arg(x); */
		t = defI (t1);
		return t;
	}
        if (used == NULL && atom (fnc(x)))
	{
                t1 = fnc(x);
                if (red_arg)
                    t2 = red1 (arg(x), red_arg);
                else
                    t2 = arg(x);
		t = ap (t1, t2);
		return t;
	}
        if (node(x) == _ap &&
            node(fnc(x)) == _ap &&
            fnc(fnc(x)) == K)
	{
                t1 = red1 (arg(fnc(x)), red_arg);
                if (red_arg)
                        t2 = red1 (arg(x), red_arg);
                else
                        t2 = arg(x);
		t = defK (t1, t2);
		return t;
	}
        if (!atom(fnc(x)) && !atom(fnc(fnc(x))) && fnc(fnc(fnc(x))) == S)
	{
		t1 = red1 (arg(fnc(fnc(x))), red_arg);
                if (red_arg)
                        t2 = red1 (arg(fnc(x)), red_arg);
                else
                        t2 = arg(fnc(x));
                if (red_arg)
                        t3 = red1 (arg(x), red_arg);
                else
                        t3 = arg(x);
		t4 = defS (t1, t2, t3);
                t5 = red1 (right(t4), red_arg);
		if (left(t5) == right(t5))
			return t4;
		t = trans (t4, t5);
		return t;
	}
	t1 = red1 (fnc(x), red_arg);
        if (red_arg)
        	t2 = red1 (arg(x), red_arg);
        else
            t2 = arg(x);
	t3 = ap (t1, t2);
	if (left(t3) == right(t3))
		return t3;
	t4 = red1 (right(t3), red_arg);
	if (left(t4) == right(t4))
		return t3;
	t = trans (t3, t4);
	return t;
}

/* 
    d : a=b
    red a: a=c
    red b: b=d
    reduc d: c=d
*/
DEM reduc (DEM ab, int red_arg)
{
DEM ac, bd, cb, cd; 
    ac = red1 (left(ab), red_arg);
    bd = red1 (right(ab), red_arg);
    cb = transym1 (ac, ab);
    cd = trans (cb, bd);
    return cd;    
}

DEM redu1 (DEM x);

DEM redu (DEM x)
{
int forme_Sfg;
DEM rf, ra, f1, a1, x1, r1, r2, t1, t2, t3, t4, t5, t6, r, rr1;
	trace_dem ("redu", x);
	if (atom(x))
        {
                trace_dem ("atom: return", x);
		return x;
        }
        trace_dem ("not atom", x);
        rf = redu (fnc(x)); trace_dem ("", rf);
        ra = redu (arg(x)); trace_dem ("", ra);
	f1 = right (rf); trace_dem ("", f1);
	a1 = right (ra); trace_dem ("", a1);
        trace_dem ("", x);
        if (fnc(x)==f1 && arg(x)==a1)
	{
		r1 = redu1 (x); trace_dem ("", r1);
                rr1 = right(r1); trace_dem ("", rr1);
		if (rr1 == x)
                {
                        trace_dem ("return", r1);
			return r1;
                }
                trace_dem ("", rr1);      
		r2 = redu (rr1); trace_dem ("", r2);
		if (left(r2) == right(r2))
			return r1;
		if (left(r1) == right(r1))
			return r2;
		r = trans (r1, r2); trace_dem ("", r);
		return r;
	}
	x1 = ap (f1, a1); trace_dem ("", x1);
	r1 = redu1 (x1); trace_dem ("", r1);
	if (right(r1) == x)
		r2 = r1;
	r2 = redu (right(r1)); trace_dem ("", r2);
	t3 = ap (rf, ra); trace_dem ("", t3);
	t4 = trans (t3, r1); trace_dem ("", t4);
	t5 = trans (t4, r2); trace_dem ("", t5);
	return t5;
}

DEM redu1 (DEM x)
{
DEM t1, t2, t3, t4, t5, t6, t7, t8, a1, a2;
int forme_SKfg;
        trace_dem ("redu1", x);
        a1 = Ext4;
        a2 = Ext5;
        forme_SKfg = !atom(x) && !atom(fnc(x))   
                        && fnc(fnc(x))==S
                        && !atom(arg(fnc(x))) 
                        && fnc(arg(fnc(x)))==K;
        if (forme_SKfg && arg(x)==I)
	{
	/* S(Kf)I = I */
                trace_dem ("S(Kf)I", x);
                t1 = arg(arg(fnc(x)));  trace_dem ("", t1);
                t2 = ap (a1, t1);       trace_dem ("", t2);
                t3 = defI (t1);         trace_dem ("", t3);
                t4 = trans (t2, t3);    trace_dem ("", t4);
                t5 = red (left(t4));    trace_dem ("", t5);
                t7 = transym1 (t5, t4);  trace_dem ("", t7);
		return t7;
	}
        if (forme_SKfg && !atom(arg(x)) && fnc(arg(x))==K)
	{
	/* S(Kf)(Ka) = K(fa) */
                trace_dem ("S(Kf)(Ka)", x);
                t1 = arg(arg(fnc(x)));  /* trace_dem ("", t1); */
                t2 = arg(arg(x));       /* trace_dem ("", t2); */
                t3 = app(a2, t1, t2);   /* trace_dem ("", t3); */
                t4 = red (left(t3));    /* trace_dem ("", t4); */
                t6 = transym1 (t4, t3);  /* trace_dem ("", t6); */
                t7 = red (right(t3));   /* trace_dem ("", t6); */
                t8 = trans (t6, t7);    /* trace_dem ("", t8); */
		return t8;
	}
	return x;
}
