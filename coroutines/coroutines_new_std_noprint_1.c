/* coroutines */

#include <stdio.h>
#include <setjmp.h>
#include <string.h>

#define int long

typedef struct duo { jmp_buf *me; jmp_buf *you; } *duo;

// int stack[10000];

char gbuf[10000] = "";

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

int start (duo us, int (*actions) (), int intro, int *stack)
{
int result;
int *sp;
	result = setjmp (*(us->me));
	if (result == 0)
	{
		// _SP = (int *)123; _SP = stack; _SP = (int *)456;
		sp = getsp();
		{
			int buf[sp-stack];
			return (*actions) (us, intro);
		}
	}
	else return result;
}

int cont (duo us, int param)
{
int result;
	result = setjmp (*(us->me));
	if (result == 0) longjmp (*(us->you), param);
	else return result;
}

int coroutine_actions (duo you_and_me, int intro)
{
struct duo us[1];
char *answer;
char lbuf[100];
	us->me = you_and_me->you;
	us->you = you_and_me->me;
	sprintf (lbuf, "First got %s from Main\n", (char *)intro);
	strcat (gbuf, lbuf);
	answer = (char *) cont (us, (int)"Fine Main, and you ?");
	sprintf (lbuf, "Then got %s from Main\n", answer);
	strcat (gbuf, lbuf);
	answer = (char *) cont (us, (int)"Nice day, isn't it ?");
	return (int)"That's all !\n";
}

int main ()
{
jmp_buf my_env, your_env;
struct duo us[1];
char *answer;
#define STACK_SIZE 10000
int stack[STACK_SIZE];
char lbuf[100];
	us->me = &my_env;
	us->you = &your_env;
	answer = (char *) start (us, coroutine_actions, (int)"Hello Coroutine, how are you ?", stack+STACK_SIZE);
	sprintf (lbuf, "First got %s from Coroutine\n", answer);
	strcat (gbuf, lbuf);
	answer = (char *) cont (us, (int)"And what else ?");
	sprintf (lbuf, "Then got %s from Coroutine\n", answer);
	strcat (gbuf, lbuf);
	printf ("%s", gbuf);
}


		
