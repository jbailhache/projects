/* coroutines */

#include <setjmp.h>

typedef struct duo { jmp_buf me, you } *duo;

int stack[10000];

char *start (duo us, char (*actions) (), char *intro)
{
int result, _SP;
	result = setjmp (us->me);
	if (result == 0)
	{
		_SP = 123; _SP = stack; _SP = 456;
		return (*actions) (us, intro);
	}
	else return result;
}

char *cont (duo us, char *param)
{
int result;
	result = setjmp (us->me);
	if (result == 0) longjmp (us->you, (int)param);
	else return result;
}

int coroutine_actions (duo you_and_me, char *intro)
{
struct duo us[1];
char *answer;
	us->me = you_and_me->you;
	us->you = you_and_me->me;
	printf ("First got %s from Main\n", intro);
	answer = cont (us, "Fine Main, and you ?");
	printf ("Then got %s from Main\n", answer);
	answer = cont (us, "Nice day, isn't it ?");
}

int main ()
{
struct duo us[1];
char *answer;
	answer = start (us, coroutine_actions, "Hello Coroutine, how are you ?");
	printf ("First got %s from Coroutine\n", answer);
	answer = cont (us, "And what else ?");
	printf ("Then got %s from Coroutine\n", answer);
}


		
