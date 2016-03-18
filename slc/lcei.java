<!DOCTYPE HTML PUBLIC "-//W3C//DTD HTML 4.0 Transitional//EN">
<!-- saved from url=(0047)http://www.webb.net/sites/log/src/lcs/lcei.java -->
<HTML><HEAD>
<META content="text/html; charset=windows-1252" http-equiv=Content-Type>
<META content="MSHTML 5.00.2014.210" name=GENERATOR></HEAD>
<BODY><XMP>public class lcei 
{
	static expr I, K, S, nil;
		   
	public static expr ap (expr f, expr a)
	{
		return new expr ("ap", 2, f, a, nil);
	}

	public static expr transym (expr d1, expr d2)
	{
		return new expr ("transym", 2, d1, d2, nil);
	}

	public static expr defI (expr a)
	{
		return new expr ("defI", 1, a, nil, nil);
	}

	public static expr defK (expr a, expr b)
	{
		return new expr ("defK", 2, a, b, nil);
	}

	public static expr defS (expr a, expr b, expr c)
	{
		return new expr ("defS", 3, a, b, c);
	}

	public static expr axm (expr a, expr b)
	{
		return new expr ("axm", 2, a, b, nil);
	}

	public static expr DBVar (int l)
	{
		return new expr ("DBVar", l, 0, nil, nil, nil);
	}

	public static expr DBLambda (expr x)
	{
		return new expr ("DBLambda", 1, x, nil, nil);
	}

	public static expr DB_Subst (expr x, expr a)
	{
		return new expr ("DB_Subst", 2, x, a, nil);
	}

	public static boolean equal (expr x, expr y)
	{
		if (x == nil)
		{
			if (y == nil)
				return true;
			return false;
		}
		if (y == nil)
			return false;
		if (!(x.node.equals(y.node)))
			return false;
		if (x.nprem != y.nprem)
			return false;
		for (int i=0; i<x.nprem; i++)
			if (!equal (x.prem[i], y.prem[i]))
				return false;
		return true;
	}

        public static expr dbshift (int m, int n, expr x)
	{
		if (x == nil)
			return nil;
		if (x.node.equals ("DBVar"))
		{
			if (x.level >= m)
				return DBVar (x.level + n);
			else
				return x;
		}
		if (x.node.equals ("DBLambda"))
			return DBLambda (dbshift (m+1, n, x.prem[0]));
		return new expr (x.node, x.level, x.nprem,
			dbshift (m, n, x.prem[0]),
			dbshift (m, n, x.prem[1]),
			dbshift (m, n, x.prem[2]));		

	}

	public static expr DBsubst (int n, expr y, expr z)
	{
		if (y == nil)
			return nil;
                if (y.node.equals ("DBVar")) 
		{
			if (y.level == n)
				return z;
			if (y.level > n)
				return DBVar (y.level - 1);
		}
		if (y.node.equals ("ap"))
			return ap (DBsubst (n, y.prem[0], z),
				   DBsubst (n, y.prem[1], z));
		if (y.node.equals ("DBLambda"))
                        return DBLambda (DBsubst (n+1, y.prem[0], dbshift (0, 1, z)));
 		return new expr (y.node, y.level, y.nprem,
			DBsubst (n, y.prem[0], z), 
			DBsubst (n, y.prem[1], z),
			DBsubst (n, y.prem[2], z));	
	}

	public static expr left (expr x)
	{
		if (x.node.equals ("ap"))
			return ap (left(x.prem[0]), left(x.prem[1]));	
		if (x.node.equals ("transym"))
		{
			if (equal (left(x.prem[0]), left(x.prem[1])))
				return right(x.prem[0]);
			return I;
		}		
		if (x.node.equals ("defI"))
			return ap (I, left(x.prem[0]));
		if (x.node.equals ("defK"))
			return ap (ap (K, left(x.prem[0])), left(x.prem[1]));
		if (x.node.equals ("defS"))
			return ap (ap (ap (S, left(x.prem[0])), left(x.prem[1])), left(x.prem[2]));
		if (x.node.equals ("axm"))
			return x.prem[0];
		if (x.node.equals ("DB_Subst"))
			return ap (DBLambda (x.prem[0]), x.prem[1]);
		return x;
			 		
	}

	public static expr right (expr x)
	{
		if (x.node.equals ("ap"))
			return ap (right(x.prem[0]), right(x.prem[1]));
		if (x.node.equals ("transym"))
		{
			if (equal (left(x.prem[0]), left(x.prem[1])))
				return right(x.prem[1]);
			return I;
		}		
		if (x.node.equals ("defI"))
			return right(x.prem[0]);
		if (x.node.equals ("defK"))
			return right(x.prem[0]);
		if (x.node.equals ("defS"))
			return ap (ap (right(x.prem[0]), right(x.prem[2])), ap (right(x.prem[1]), right(x.prem[2])));
		if (x.node.equals ("axm"))
			return x.prem[1];
		if (x.node.equals ("DB_Subst"))
			return DBsubst (0, x.prem[0], x.prem[1]);	
		return x;
	}
	
	public boolean atom (expr x)
	{
		if (x.node.equals ("ap"))
			return false;
		return true;
	}
	
	expr transym1 (expr ab, expr cd)
	{
		if (equal (ab, cd))
			return right (ab);
		if (equal (left(ab), right(ab)))
			return cd;
		return transym (ab, cd); 
	}	

	expr sym (expr ab)
	{
		return transym1 (ab, left(ab));	
	}

	expr trans (expr ab, expr bc)
	{
		return transym1 (sym(ab), bc);
	}

	public static void main (String args[])
	{
		nil = (expr) null;
		I = new expr ("I", 0, nil, nil, nil);
		K = new expr ("K", 0, nil, nil, nil);
		S = new expr ("S", 0, nil, nil, nil);

		expr x;
		x = ap (K, ap (S, I));
		x.print (System.out);
		System.out.println ("---");
		x = defI (K);
		left(x).print (System.out);
		System.out.println ("");
		x = transym (ap(S,K), ap(S,K));
		left(x).print (System.out);
		System.out.println ("");
		x = DB_Subst (DBVar(0), K);
		left(x).print (System.out);
		System.out.print (" = ");
		right(x).print (System.out);


	}
}
 
</XMP></BODY></HTML>
