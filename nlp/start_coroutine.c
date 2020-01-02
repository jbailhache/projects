
#include "coroutines.h"

int start_coroutine (struct coroutine *cr,
	int (*f) (/* void *p, struct coroutine *cr */),
	void *p, int *stack)
{
int x, y;
int *_SP;
int test;
	x = setjmp (*(cr->calling));
	if (x == 0)
	{
		test = 123;
		_SP = stack;
		test = 456;
		y = (*f) (p, cr);
		return y;
	}
	else
	{
		return x;
	}
}


