
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

typedef long expr;

int ispair (expr x)
{
	return x < 0;
}

int isatom (expr x)
{
	return x >= 0;
}

expr atom (char *s)
{
	expr x;
	x = *(int *)s;
	if (x < 0 || strlen(s) >= sizeof(expr))
	{
		printf ("Bad name for atom: %s\n", s);
		exit(0);
	}
	return x;
}

struct pair
{
	expr fst, snd;
};

#define SIZE 10000

int npairs = 0;

struct pair mem[SIZE];

expr fst (expr x)
{
	if (!ispair(x))
	{
		printf ("fst of not pair 0x%X\n", x);
		exit(0);
	}
	return mem[-x-1].fst;
}

expr snd (expr x)
{
	if (!ispair(x))
	{
		printf ("fst of not pair 0x%X\n", x);
		exit(0);
	}
	return mem[-x-1].snd;
}

expr newpair (expr x, expr y)
{
	if (npairs >= SIZE)
	{
		printf("Overflow\n");
		exit(0);
	}
	mem[npairs].fst = x;
	mem[npairs].snd = y;
	npairs++;
	return -npairs;
}

expr findpair (expr x, expr y)
{
	int i;
	for (i=0; i<npairs; i++)
	{
		if (mem[i].fst == x && mem[i].snd == y)
			return -i-1;
	}
	return 0;
}

expr pair (expr x, expr y)
{
	expr z;
	z = findpair (x, y);
	if (z)
		return z;
	else
		return newpair (x, y);
}

expr eq (expr x, expr y)
{
	return x == y;
}

struct charwriter
{
	int (*f) (struct charwriter *, char);
};

int writechar (struct charwriter *cw, char c)
{
	return (*(cw->f))(cw,c);
}

void writeexpr (struct charwriter *cw, expr x)
{
	char s[sizeof(expr)+1];
	int i;
	if (isatom(x))
	{
		for (i=0; i<sizeof(s); i++)
			s[i] = 0;
		memcpy (s, &x, sizeof(s));
		for (i=0; s[i]; i++)
			writechar(cw,s[i]);
	}
	else
	{
		writechar(cw,'-');
		writeexpr(cw,fst(x));
		writechar(cw,' ');
		writeexpr(cw,snd(x));
	}
	
}

expr zero, suc, H, H1, R1, R2, R3, Psi, lim, w;

#define ap(x,y) pair(x,y)
#define fnc(x) fst(x)
#define arg(x) snd(x)
#define isap(x) ispair(x)
#define isnap(x) isatom(x)

init ()
{
	zero = atom("0");
	suc = atom("suc");
	H = atom("H");
	H1 = atom("H1");
	R1 = atom("R1");
	R2 = atom("R2");
	R3 = atom("R3");
	Psi = atom("psi");
	lim = atom("lim");
	w = ap(ap(H,suc),zero);
}

expr first (expr a)
{
	if (isnap(a))
		return ap(atom("fst"),a);
	if (isap(fnc(a)) && eq(H,fnc(fnc(a))))
		return arg(a);
	if (isap(fnc(a)) && eq(R1,fnc(fnc(a))))
		return arg(a);
	if (isap(fnc(a)) && isap(fnc(fnc(a))) && eq(R2,fnc(fnc(fnc(a)))))
		return arg(a);
	return ap(first(fnc(a)),arg(a));
}

expr next (expr a)
{
	if (isnap(a))
		return ap(atom("nxt"),a);
	if (isap(fnc(a)) && eq(H,fnc(fnc(a))))
		return ap(fnc(a),ap(arg(fnc(a)),arg(a)));
	if (eq(R1,fnc(a)))
		return ap(ap(R1,arg(a)),arg(a));
	if (isap(fnc(a)) && eq(R2,fnc(fnc(a))))
		return ap(ap(a,arg(fnc(a))),arg(a));
	return ap(next(fnc(a)),arg(a));
}

expr subst (expr s, expr z, expr a)
{
	if (eq(zero,a))
		return z;
	if (eq(suc,a))
		return s;
	if (isnap(a))
		return a;
	return ap(subst(s,z,fnc(a)),subst(s,z,arg(a)));
}

expr limit (expr a, expr b, expr c)
{
	if (isap(b) && 
            eq(a,arg(b)) && 
            isap(c) && 
            eq(fnc(b),fnc(c)) && 
	    eq(b,arg(c)))
		return ap(ap(H,fnc(b)),a);  
	if (isap(b) &&
            eq(a,arg(b)) &&
            isap(c) &&
            eq(a,arg(c)) &&
            isap(fnc(c)) &&
            eq(fnc(b),fnc(fnc(c))) &&
            eq(fnc(b),arg(fnc(c))))
		return ap(ap(R1,fnc(b)),a);
	if (isap(b) &&
            eq(a,arg(b)) &&
            isap(c) &&
            eq(a,arg(c)) &&
            isap(fnc(c)) &&
            isap(fnc(fnc(c))) &&
            eq(fnc(b),fnc(fnc(fnc(c)))) &&
            isap(fnc(b)) &&
            eq(arg(fnc(b)),arg(fnc(c))) &&
            eq(fnc(fnc(b)),arg(fnc(fnc(c)))))
		return ap(ap(ap(R2,fnc(fnc(b))),arg(fnc(b))),a);
	if (isap(a) && isap(b) && isap(c) &&
            eq(arg(a),arg(b)) && eq(arg(b),arg(c)))
		return ap(limit(fnc(a),fnc(b),fnc(c)),arg(a));         
	return ap(ap(ap(lim,a),b),c);
}

#define MAXMEMO SIZE

int nmemo = 0;

struct item
{
	expr arg;
	expr val;
};

struct item memo[MAXMEMO];

int count = 0;

int cwf_putchar (struct charwriter *cw, char c)
{
	return putchar(c);
}

expr psi1 (expr a);

expr psi (expr a)
{
	expr b;
	struct charwriter cw;
	int i;
	for (i=0; i<nmemo; i++)
	{
		if (eq(a,memo[i].arg))
			return memo[i].val;
	}
	b = psi1(a);
	memo[nmemo].arg = a;
	memo[nmemo].val = b;
	nmemo++;
	cw.f = cwf_putchar;
	count++;
	printf (" %d : psi ", count);
	writeexpr (&cw, a);
	printf (" = ");
	writeexpr (&cw, b);
	printf ("\n");
	return b;
}

expr psi1 (expr a)
{
	if (eq(zero,a))
		return w;
	if (isnap(a))
		return ap(Psi,a);	
	if (eq(suc,fnc(a)))
	{
		expr c;
		c = psi(arg(a));
		if (isap(c) && eq(zero,arg(c)) && isap(fnc(c)) && eq(suc,arg(fnc(c))))
			return ap(ap(ap(R1,fnc(fnc(c))),suc),zero);
	}	
	if (isnap(fnc(a)))
		return ap(Psi,a);
	if (eq(H1,fnc(fnc(a))))
	{
		expr b, c, d;
		b = ap(suc,zero);
		c = psi(ap(arg(fnc(a)),arg(a)));
		d = psi(subst(arg(fnc(a)),arg(a),c));
		return limit(b,c,d);
	}		
	/*if (eq(H,fnc(fnc(a))))
		return limit (
			psi(arg(a)), 
			psi(ap(arg(fnc(a)),arg(a))), 
			psi(ap(arg(fnc(a)),ap(arg(fnc(a)),arg(a))))
			);*/
	return limit (psi(first(a)), psi(first(next(a))), psi(first(next(next(a)))));
	//return ap(Psi,a);
}

dump ()
{
	int i;
	for (i=0; i<npairs; i++)
	{
		printf(" %4d %08X : %08X %08X \n", i, -i-1, mem[i].fst, mem[i].snd);
	}
}

main ()
{
	struct charwriter cw;
	cw.f = cwf_putchar;

	printf(" %d ", sizeof(expr));
	expr x;
	x = pair (pair (atom("abc"), atom("def")), atom("ghi"));
	// x = pair (atom("abc"), atom("def"));
	printf("x = %d\n",x);
	printf("mem: %X %X\n", mem[0].fst, mem[0].snd);
	writeexpr(&cw,x);

	printf("\n");
	
	init(); 

	expr a, b, c, d, f;
	a = ap(ap(H,suc),zero);
	b = next(a);
	printf ("b = ");
	writeexpr(&cw,b);
	printf("\n");

	a = ap(ap(ap(R1,H),suc),zero);
	b = first(next(next(a)));
	printf ("b = ");
	writeexpr(&cw,b);
	printf("\n");

	a = ap(ap(ap(ap(R2,R1),H),suc),zero);
	b = first(next(next(a)));
	printf ("b = ");
	writeexpr(&cw,b);
	printf("\n");

	x = atom("x");
	f = atom("f");
	a = x;
	b = ap(f,a);
	c = ap(f,b);
	d = limit(a,b,c);
	printf ("d = ");
	writeexpr(&cw,d);
	printf("\n");
	//a = ap(suc,ap(suc,zero));
	//a = ap(ap(ap(H,H),suc),zero);
	//a = ap(ap(ap(R1,H),suc),zero);
	a = ap(ap(H1,suc),zero);
	//a = ap(ap(H1,suc),ap(ap(H1,suc),zero));
	b = psi(a);
	//dump();
	printf ("\na=%X b=%X\n",a,b);
	printf("psi ");
	writeexpr(&cw,a);
	printf (" = ");
	writeexpr(&cw,b);
	printf("\n");

	printf("npairs = %d\n", npairs);


}
