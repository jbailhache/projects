/* coroutines */

#include <stdlib.h>
#include <stdio.h>
#include <setjmp.h>
#include <string.h>

#define STACK_SIZE 1000

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

int start (jmp_buf *me, jmp_buf *you, jmp_buf *mainprog, int (*actions) (), int intro, int *stack)
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
			return (*actions) (me, you, mainprog, intro);
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

int coroutine_actions (jmp_buf *you, jmp_buf *me, jmp_buf *mainprog, int intro)
{
char *answer;
char buf[100];
	printf ("First Coroutine got '%s' from Main\n", (char *)intro);
	strcpy (buf, (char *)intro);
	// answer = (char *) cont (me, mainprog, (int)buf);
	answer = (char *) cont (me, you, (int)"Coroutine says to Maincor : Fine Main, and you ?");
	printf ("Then Coroutine got '%s' from Main\n", answer);
	strcpy (buf, answer);
	// answer = (char *) cont (me, mainprog, (int)buf);
	answer = (char *) cont (me, you, (int)"Coroutine says to Maincor : Nice day, isn't it ?");
	return (int)"That's all !";
}

int maincor_actions (jmp_buf *yourself_mainprog, jmp_buf *myself, jmp_buf *mainprog, int intro)
{
jmp_buf me[1], you[1];
char *answer;
//#define STACK_SIZE 1000
//int stack[STACK_SIZE];
int *stack;
	// printf ("Maincor receives %s from Main\n", (char *) intro);
	answer = (char *) cont (myself, mainprog, (int)"OK Main !");
	// printf ("Then Maincor receives %s from Main\n", answer);
	stack = (int *) calloc (STACK_SIZE+1, sizeof(int));
	answer = (char *) start (myself, you, mainprog, coroutine_actions, (int)"Maincor says to Coroutine : Hello Coroutine, how are you ?", stack+STACK_SIZE);
	// printf ("First got %s from Coroutine\n", answer);
	answer = (char *) cont (myself, mainprog, (int)answer);
	answer = (char *) cont (myself, you, (int)"Maincor says to Coroutine : And what else ?");
	// printf ("Then got %s from Coroutine\n", answer);
	answer = (char *) cont (myself, mainprog, (int)answer);
	return (int)"Done !";
}

int main ()
{
jmp_buf me[1], you[1];
char *answer;
//#define STACK_SIZE 1000
//int stack[STACK_SIZE];
int *stack;
	stack = (int *) calloc (STACK_SIZE+1, sizeof(int));
	answer = (char *) start (me, you, me, maincor_actions, (int)"Hello Maincor, it's up to you !", stack+STACK_SIZE);
	for (;;)
	{
		printf ("Main got : %s\n", answer);
		if (!strcmp (answer, "Done !"))
			break;
		answer = (char *) cont (me, you, (int)"OK, go on !");
	}
}

		
