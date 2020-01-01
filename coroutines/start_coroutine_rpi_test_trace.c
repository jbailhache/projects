/* coroutines */

#include <setjmp.h>

struct coroutine
{
	jmp_buf *calling;
	jmp_buf *env;
};

int start_coroutine (struct coroutine *cr,
	int (*f) (/* void *p, struct coroutine *cr */),
	void *p, int *stack)
{
int x, y;
struct coroutine *calling;
int *_SP;
int test;
	printf ("start_coroutine(0x%X,0x%X,0x%X,0x%X)\n",cr,f,p,stack);
    	calling = malloc (sizeof(*calling));
	printf ("calling=0x%X\n",calling);
	x = setjmp (*(cr->calling));
	printf("x=0x%X\n",x);
	if (x == 0)
	{
		printf("then\n");
		calling->calling = cr->env;
		calling->env = cr->calling;
		printf("set sp\n");
		test = 123;
		_SP = stack;
		test = 456;
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

