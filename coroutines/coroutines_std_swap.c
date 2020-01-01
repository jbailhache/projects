/* coroutines */

#include <stdio.h>
#include <setjmp.h>

typedef struct coroutine { jmp_buf *caller; jmp_buf *called; } *coroutine;

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

int start (coroutine cr, int (*actions) (), int intro, int *stack)
{
int result;
int *sp;
	struct coroutine cr1[1];
	cr1->caller = cr->called;
	cr1->called = cr->caller;
	result = setjmp (*(cr->caller));
	if (result == 0)
	{
		// _SP = (int *)123; _SP = stack; _SP = (int *)456;
		sp = getsp();
		{
			int buf[sp-stack];
			return (*actions) (cr1, intro);
		}
	}
	else return result;
}

int cont (coroutine cr, int param)
{
int result;
	result = setjmp (*(cr->caller));
	if (result == 0) longjmp (*(cr->called), param);
	else return result;
}

int coroutine_actions (coroutine you1, int intro)
{
struct coroutine you[1];
char *answer;
	//you->caller = me->called;
	//you->called = me->caller;
	you->caller = you1->caller;
	you->called = you1->called;
	printf ("First got %s from Main\n", (char *)intro);
	answer = (char *) cont (you, (int)"Fine Main, and you ?");
	printf ("Then got %s from Main\n", answer);
	answer = (char *) cont (you, (int)"Nice day, isn't it ?");
	return (int)"That's all !\n";
}

int main ()
{
jmp_buf my_env, your_env;
struct coroutine cr[1];
char *answer;
#define STACK_SIZE 1000
int stack[STACK_SIZE];
	cr->caller = &my_env;
	cr->called = &your_env;
	answer = (char *) start (cr, coroutine_actions, (int)"Hello Coroutine, how are you ?", stack+STACK_SIZE);
	printf ("First got %s from Coroutine\n", answer);
	answer = (char *) cont (cr, (int)"And what else ?");
	printf ("Then got %s from Coroutine\n", answer);
}


		
