/* coroutines */

#include <stdio.h>
#include <setjmp.h>

typedef struct coroutine
{
	jmp_buf *calling;
	jmp_buf *env;
} *duo;

int start_coroutine (duo cr,
	int (*f) (),
	int p, int *stack)
{
int x, y;
int *_SP;
	x = setjmp (*(cr->calling));
	if (x == 0)
	{
		_SP = (int *)123; _SP = stack; _SP = (int *)456;
		y = (*f) (cr, p);
		return y;
	}
	else
	{
		return x;
	}
}

int call_coroutine (duo cr, int entree)
{
int x;
	x = setjmp (*(cr->calling));
	if (x == 0)
	{
		longjmp (*(cr->env), entree);
		printf ("Error calling coroutine\n");
	}
	else
	{
		return x;
	}
}

int coroutine1 (duo me, int p)
{
char  *x;
struct coroutine calling[1];
	calling->calling = me->env;
	calling->env = me->calling;
	printf ("Lancement coroutine avec parametre <%s>\n", (char *)p);
	x = (char *) call_coroutine (calling, (int)"1er parametre coroutine->appelant");
	printf ("Appelant retourne <%s> la 1ere fois\n", x);
	x = (char *) call_coroutine (calling, (int)"2eme parametre coroutine->appelant");
	printf ("Appelant retourne <%s> la 2eme fois\n", x);
	/* return "Fin coroutine"; */
	// x = (char *) call_coroutine (calling, (int)"3eme parametre coroutine->appelant");
	return (int)"That's all !\n";
}

int test_coroutine ()
{
struct coroutine cr[1];
jmp_buf calling, env;
#define STACK_SIZE 1000
int stack [STACK_SIZE];
char *x;
	cr->calling = &calling;
	cr->env = &env;
	x = (char *) start_coroutine (cr, coroutine1, (int)"Parametre lancement",
		stack + STACK_SIZE);
	printf ("Lancement retourne <%s>\n", x);
	x = (char *) call_coroutine (cr, (int)"1er appel");
	printf ("1er appel retourne <%s>\n", x);
	// x = (char *) call_coroutine (cr, (int)"2eme appel");
	// printf ("2eme appel retourne <%s>\n", x);

}

int main ()
{
	test_coroutine ();
}



