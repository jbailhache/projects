/* coroutines */

#include <setjmp.h>

struct coroutine
{
	jmp_buf *calling;
	jmp_buf *env;
};

int start_coroutine (struct coroutine *cr,
	int (*f) (/* void *p, struct coroutine *cr */),
	void *p, int *stack)
{
int x, y;
	x = setjmp (*(cr->calling));
	if (x == 0)
	{
		_SP = stack; /* restaurer la pile ? */
		y = (*f) (p, cr);
		return y;
	}
	else
	{
		return x;
	}
}

int call_coroutine (struct coroutine *cr, int entree)
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

int coroutine1 (char *p, struct coroutine *me)
{
int x;
struct coroutine calling;
	calling.calling = me->env;
	calling.env = me->calling;
	printf ("Lancement coroutine avec parametre <%s>\n", p);
	x = call_coroutine (&calling, (int)"1er parametre coroutine->appelant");
	printf ("Appelant retourne <%s> la 1ere fois\n", x);
	x = call_coroutine (&calling, (int)"2eme parametre coroutine->appelant");
	printf ("Appelant retourne <%s> la 2eme fois\n", x);
	/* return "Fin coroutine"; */
	x = call_coroutine (&calling, (int)"3eme parametre coroutine->appelant");
}

test_coroutine ()
{
struct coroutine cr;
jmp_buf calling, env;
#define STACK_SIZE 1000
int stack [STACK_SIZE];
int x;
	cr.calling = &calling;
	cr.env = &env;
	x = start_coroutine (&cr, coroutine1, (int)"Parametre lancement",
		stack + STACK_SIZE);
	printf ("Lancement retourne <%s>\n", x);
	x = call_coroutine (&cr, (int)"1er appel");
	printf ("1er appel retourne <%s>\n", x);
	x = call_coroutine (&cr, (int)"2eme appel");
	printf ("2eme appel retourne <%s>\n", x);

}

main ()
{
	test_coroutine ();
}



