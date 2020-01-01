/* coroutines */

#include <stdlib.h>
#include <stdio.h>
#include <setjmp.h>

// int stack[10000];

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

int start (jmp_buf *me, jmp_buf *you, int (*actions) (), int intro, int *stack)
{
int result;
int *sp;
	result = setjmp (*me);
	if (result == 0)
	{
		// _SP = (int *)123; _SP = stack; _SP = (int *)456;
		sp = getsp();
		{
			int buf[sp-stack];
			return (*actions) (me, you, intro);
		}
	}
	else return result;
}

int cont (jmp_buf *me, jmp_buf *you, int param)
{
int result;
	result = setjmp (*me);
	if (result == 0) longjmp (*you, param);
	else return result;
}

int coroutine_actions (jmp_buf *you, jmp_buf *me, int intro)
{
char *answer;
	printf ("First got %s from Main\n", (char *)intro);
	answer = (char *) cont (me, you, (int)"Fine Main, and you ?");
	printf ("Then got %s from Main\n", answer);
	answer = (char *) cont (me, you, (int)"Nice day, isn't it ?");
	return (int)"That's all !\n";
}

int main ()
{
jmp_buf me[1], you[1];
char *answer;
#define STACK_SIZE 1000
//int stack[STACK_SIZE];
int *stack;
	stack = (int *) calloc (STACK_SIZE, sizeof(int));
	answer = (char *) start (me, you, coroutine_actions, (int)"Hello Coroutine, how are you ?", stack+STACK_SIZE);
	printf ("First got %s from Coroutine\n", answer);
	answer = (char *) cont (me, you, (int)"And what else ?");
	printf ("Then got %s from Coroutine\n", answer);
}


		
