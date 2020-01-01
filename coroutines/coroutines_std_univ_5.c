/* coroutines */

#include <stdlib.h>
#include <stdio.h>
#include <setjmp.h>
#include <string.h>

typedef struct coroutine { jmp_buf *caller; jmp_buf *called; } *coroutine;

// int stack[10000];

#define STACK_SIZE 1000

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

int start (coroutine cr, coroutine mainprog, int (*actions) (), int intro, int *stack)
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
			return (*actions) (cr, mainprog, intro);
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

int coroutine_actions (coroutine me, coroutine mainprog, int intro)
{
struct coroutine you[1];
char *answer;
	you->caller = me->called;
	you->called = me->caller;
	printf ("First got %s from Main\n", (char *)intro);
	answer = (char *) cont (mainprog, intro);
	answer = (char *) cont (you, (int)"Fine Main, and you ?");
	printf ("Then got %s from Main\n", answer);
	answer = (char *) cont (mainprog, (int)answer);
	answer = (char *) cont (you, (int)"Nice day, isn't it ?");
	return (int)"That's all !\n";
}

int maincor_actions (coroutine me, coroutine mainprog, int intro)
{
jmp_buf my_env, your_env;
struct coroutine cr[1];
char *answer;
//#define STACK_SIZE 1000
//int stack[STACK_SIZE];
int *stack;
	//mainprog->caller = me->called;
	//mainprog->called = me->caller;
	printf ("Maincor receives %s from Main\n", (char *)intro);
	answer = (char *) cont (mainprog, (int)"OK, Main !");
	stack = (int *) calloc (STACK_SIZE+1, sizeof(int));
	cr->caller = &my_env;
	cr->called = &your_env;
	answer = (char *) start (cr, mainprog, coroutine_actions, (int)"Hello Coroutine, how are you ?", stack+STACK_SIZE);
	// printf ("First got %s from Coroutine\n", answer);
	answer = (char *) cont (mainprog, (int)answer);
	answer = (char *) cont (cr, (int)"And what else ?");
	// printf ("Then got %s from Coroutine\n", answer);
	answer = (char *) cont (mainprog, (int)answer);
	return (int)"Done !";
}

int main ()
{
jmp_buf my_env, your_env;
struct coroutine cr[1], mainprog[1];
char *answer;
//#define STACK_SIZE 1000
//int stack[STACK_SIZE];
int *stack;
	stack = (int *) calloc (STACK_SIZE+1, sizeof(int));
	cr->caller = &my_env;
	cr->called = &your_env;
	mainprog->caller = &your_env;
	mainprog->called = &my_env;
	answer = (char *) start (cr, mainprog, maincor_actions, (int)"It's up to you, Maincor !", stack+STACK_SIZE);
	for (;;)
	{
		printf ("Main got '%s' from Maincor\n", answer);
		if (!strcmp(answer,"Done !"))
			break;
		answer = (char *) cont (cr, (int)"Go on, Maincor !");
	}
}

		
