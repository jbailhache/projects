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
	printf ("start_coroutine(0x%X,0x%X,0x%X,0x%X)\n",cr,f,p,stack);
	x = setjmp (*(cr->calling));
	printf("x=0x%X\n",x);
	if (x == 0)
	{
		printf("then\n");
		_SP = stack;
		printf("sp modified, call function\n");
		y = (*f) (p, cr);
		printf("y=0x%X\n",y);
		return y;
	}
	else
	{
		printf("else\n");
		return x;
	}
}

