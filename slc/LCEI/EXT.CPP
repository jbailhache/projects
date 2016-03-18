
#include "lctm.h"
 
DEM transym_redu (DEM ab, DEM cd)
{
DEM ae, cf, fc, eb, fd, bd;
    if (ab == cd)
        return right (ab);
    if (left(ab) == left(cd))
    {
        bd = transym (ab, cd);
    }
    else
    {
        ae = redu (left(ab));
        eb = transym (ae, ab); 
        cf = redu (left(cd));
        fd = transym (cf, cd);
        bd = transym (eb, fd);
    }
    return bd;
}

DEM ext (DEM x, DEM t)
{
DEM ext_I, ext_K, ext_S, te, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10;
	trace_dem ("ext", x);
	trace_dem ("ext", t);
	ext_I = Ext1;
	ext_K = Ext2;
	ext_S = Ext3;
	if (t == x)
	{
		trace_dem ("return", I);
		return I;
	}
	if (!in (x, left(t)) && !in (x, right(t)))
	{
		te = ap (K, t);
                trace_dem ("", te);
		return te;
	}
        if (node(t) == _ap && subdem(1,t) == x &&
                !in (x, left(subdem(0,t))) && !in (x, right(subdem(0,t))))
                return subdem(0,t);
	switch (node(t))
	{
		case _transym:
                        trace_dem ("transym", t);
			t1 = ext (x, subdem(0,t)); trace_dem ("", t1);
			t2 = ext (x, subdem(1,t)); trace_dem ("", t2);
                        trace_dem ("", t1);
                        trace_dem ("transym", t);
                        te = transym_redu (t1, t2); trace_dem ("", te);
			return te;

		case _ap:
                        trace_dem ("ap", t);
			t1 = ext (x, subdem(0,t)); trace_dem ("", t1);
			t2 = ext (x, subdem(1,t)); trace_dem ("", t2);
			te = app (S, t1, t2); trace_dem ("", te);
			return te;

		case _defI:
                        trace_dem ("defI", t);
			t1 = ext (x, subdem(0,t)); trace_dem ("", t1);
			te = trans (ap (ext_I, t1), defI (right(t1)));
			trace_dem ("", te);
			return te;		

		case _defK:
                        trace_dem ("defK", t);
			t1 = ext (x, subdem(0,t)); trace_dem ("", t1);
			t2 = ext (x, subdem(1,t)); trace_dem ("", t2);
			t3 = app (ext_K, t1, t2); trace_dem ("", t3);
			t4 = defK (right(t1), right(t2)); trace_dem ("", t4);
			t5 = trans (t3, t4); trace_dem ("", t5);
			t6 = red (left(t5)); trace_dem ("", t6);
			t7 = transym1 (t6, t5); trace_dem ("", t7);
			return t7;

		case _defS:
                        trace_dem ("defS", t);
			t1 = ext (x, subdem(0,t)); trace_dem ("", t1);
			t2 = ext (x, subdem(1,t)); trace_dem ("", t2);
			t3 = ext (x, subdem(2,t)); trace_dem ("", t3);
			t4 = appp (ext_S, t1, t2, t3); trace_dem ("", t4);
			t5 = red (left(t4)); trace_dem ("", t5);
			t7 = transym1 (t5, t4); trace_dem ("", t7);
			t8 = red (right(t7)); trace_dem ("", t8);
			t9 = trans (t7, t8); trace_dem ("", t9);
			return t9;
		
		default:
			trace_dem ("return", I);
			return I;
	}
}

DEM exten (DEM v, DEM t)
{
DEM ax1, ax2, ext_I, ext_K, ext_S, x, y, t1, t2, t3, t4, t5, t6; 
	ax1 = Ext4;
	ax2 = Ext5;
	ext_I = Ext1;
	ext_K = Ext2;
	ext_S = Ext3;
	t1 = ext (v, t);
        trace_dem ("", t1);
	x = left(t1);
        trace_dem ("", x);
	y = right(t1);
        trace_dem ("", y);
	t2 = redu (x);
        trace_dem ("", t2);
	t3 = redu (y);
        trace_dem ("", t3);
	t5 = transym1 (t2, t1);
        trace_dem ("", t5);
	t6 = trans (t5, t3);
        trace_dem ("", t6);
	return t6;
}
