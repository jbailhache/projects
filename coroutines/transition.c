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
	answer = (char *) cont (us, (int)"Nice day, isn't it ?");
	return (int)"That's all !\n";
}

int main ()
{
jmp_buf my_env, your_env; 
struct duo us[1];
char *answer;
#define STACK_SIZE 1000
int stack [1000];
	us->me = &my_env;
	us->you = &your_env;
	answer = (char *) start (us, coroutine_actions, (int)"Hello Coroutine, how are you ?", stack + STACK_SIZE);
	printf ("First got %s from Coroutine\n", answer);
	answer = (char *) cont (us, (int)"And what else ?");
	printf ("Then got %s from Coroutine\n", answer);
	// x = (char *) cont (cr, (int)"2eme appel");
	// printf ("2eme appel retourne <%s>\n", x);

}




