
#include <stdlib.h>
#include <stdio.h>

struct s_term
{
	struct s_term * (*f) (struct s_term *, struct s_term *);
	struct s_term *p;
};

typedef struct s_term *term;

term make_term()
{
 term x;
 x = malloc (sizeof(struct s_term));
 return x;
}

term fI (term p, term x)
{
 return x;
}

term fKx (term p, term y)
{
 return p;
}

term fK (term p, term x)
{
 term Kx;
 Kx = make_term();
 Kx->f = fKx;
 Kx->p = x;
 return Kx;
}

term apply (term f, term x)
{
 return f->f(f->p, x);
}

term I, K;

init ()
{
 I = make_term();
 I->f = fI;
 K = make_term();
 K->f = fK;
}

main()
{
 term a, b, c, d;
 init();
 a = make_term();
 b = make_term();
 c = apply (K, a);
 d = apply (c, b);
 if (d == a)
  printf ("ok\n");
 else
  printf ("ko\n");
}

