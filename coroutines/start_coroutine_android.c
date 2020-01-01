/* coroutines */

#include <setjmp.h>

struct coroutine
{
	jmp_buf *calling;
	jmp_buf *env;
};
int _SP;
int start_coroutine (struct coroutine *cr,
	int (*f) (/* void *p, struct coroutine *cr */),
	void *p, int *stack)
{
int x, y;
	x = setjmp (*(cr->calling));
	if (x == 0)
	{
		_SP = stack;
		y = (*f) (p, cr);
		return y;
	}
	else
	{
		return x;
	}
}

