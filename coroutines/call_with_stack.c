
#define SIZE 1000

#include <stdio.h>

int *getsp ()
{
int *a;
	a = (int *)&a;
	a += 3;
	return a;
}

int call_with_stack (int *stack, int (*f)(), int x)
{
int *sp;
	sp = getsp();
	{
		int buf[sp-stack];
		return (*f) (x);
	}
}

int f (int x)
{
	return x*2+1;
}

int main ()
{
int stack[SIZE+8];
int a;
	a = call_with_stack (stack+SIZE, f, 123);
	printf ("a=%d\n", a);
}

