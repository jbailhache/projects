/* coroutines */

#include <stdio.h>
#include <setjmp.h>

typedef struct coroutine { jmp_buf *caller; jmp_buf *called; } *coroutine;

// int stack[10000];

char *jmpval;

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

char *start (coroutine cr, char *(*actions) (), char *intro, int *stack)
{
int result;
int *sp;
	result = setjmp (*(cr->caller));
	if (result == 0)
	{
		// _SP = (int *)123; _SP = stack; _SP = (int *)456;
		sp = getsp();
		{
			int buf[sp-stack];
			return (*actions) (cr, intro);
		}
	}
	else return jmpval;
}

char *cont (coroutine cr, char *param)
{
int result;
	result = setjmp (*(cr->caller));
	if (result == 0) 
	{
		jmpval = param;
		longjmp (*(cr->called), 1);
	}
	else return jmpval;
}

char *coroutine_actions (coroutine me, char *intro)
{
struct coroutine you[1];
char *answer;
	you->caller = me->called;
	you->called = me->caller;
	printf ("First got %s from Main\n", intro);
	answer = cont (you, "Fine Main, and you ?");
	printf ("Then got %s from Main\n", answer);
	answer = cont (you, "Nice day, isn't it ?");
	return "That's all !\n";
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
	answer = start (cr, coroutine_actions, "Hello Coroutine, how are you ?", stack+STACK_SIZE);
	printf ("First got %s from Coroutine\n", answer);
	answer = cont (cr, "And what else ?");
	printf ("Then got %s from Coroutine\n", answer);
}


		
