/* coroutines */

#include <stdio.h>
#include <setjmp.h>

typedef struct duo { jmp_buf *me; jmp_buf *you; } *duo;

int start (duo us, int (*actions) (), int intro, int *stack)
{
int result, y;
int *_SP;
	result = setjmp (*(us->me));
	if (result == 0)
	{
		_SP = (int *)123; _SP = stack; _SP = (int *)456;
		return (*actions) (us, intro);
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
char  *answer;
	us->me = you_and_me->you;
	us->you = you_and_me->me;
	printf ("First got %s from Main\n", (char *)intro);
	answer = (char *) cont (us, (int)"Fine Main, and you ?");
	printf ("Then got %s from Main\n", answer);
	answer = (char *) cont (us, (int)"2eme parametre coroutine->appelant");
	return (int)"That's all !\n";
}

int test_coroutine ()
{
struct duo cr[1];
jmp_buf calling, env;
#define STACK_SIZE 1000
int stack [STACK_SIZE];
char *x;
	cr->me = &calling;
	cr->you = &env;
	x = (char *) start (cr, coroutine_actions, (int)"Parametre lancement",
		stack + STACK_SIZE);
	printf ("Lancement retourne <%s>\n", x);
	x = (char *) cont (cr, (int)"1er appel");
	printf ("1er appel retourne <%s>\n", x);
	// x = (char *) cont (cr, (int)"2eme appel");
	// printf ("2eme appel retourne <%s>\n", x);

}

int main ()
{
	test_coroutine ();
}



