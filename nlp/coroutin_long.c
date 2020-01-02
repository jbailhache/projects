/* coroutines */

#include <setjmp.h>

void *jmpval;

struct coroutine
{
	jmp_buf *calling;
	jmp_buf *env;
};

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

void *start_coroutine (struct coroutine *cr,
	void *(*f) (/* void *p, struct coroutine *cr */),
	void *p, int *stack)
{
int x, y;
int *_SP;
int test;
	x = setjmp (*(cr->calling));
	if (x == 0)
	{
		//test = 123;
		//_SP = stack;
		//test = 456;
		_SP = getsp();
		{
			int buf[_SP-stack];		
			y = (*f) (p, cr);
			return y;
		}
	}
	else
	{
		return jmpval;
	}
}

void *call_coroutine (struct coroutine *cr, void *entree)
{
int x;
	x = setjmp (*(cr->calling));
	if (x == 0)
	{
		jmpval = entree;
		longjmp (*(cr->env), 1);
		printf ("Error calling coroutine\n");
	}
	else
	{
		return jmpval;
	}
}

int coroutine1 (char *p, struct coroutine *me)
{
void *x;
struct coroutine calling;
	calling.calling = me->env;
	calling.env = me->calling;
	printf ("Lancement coroutine avec parametre <%s>\n", p);
	x = call_coroutine (&calling, "1er parametre coroutine->appelant");
	printf ("Appelant retourne <%s> la 1ere fois\n", x);
	x = call_coroutine (&calling, "2eme parametre coroutine->appelant");
	printf ("Appelant retourne <%s> la 2eme fois\n", x);
	/* return "Fin coroutine"; */
	x = call_coroutine (&calling, "3eme parametre coroutine->appelant");
}

test_coroutine ()
{
struct coroutine cr;
jmp_buf calling, env;
#define STACK_SIZE 1000
int stack [STACK_SIZE];
void *x;
	cr.calling = &calling;
	cr.env = &env;
	x = start_coroutine (&cr, coroutine1, "Parametre lancement",
		stack + STACK_SIZE);
	printf ("Lancement retourne <%s>\n", x);
	x = call_coroutine (&cr, "1er appel");
	printf ("1er appel retourne <%s>\n", x);
	x = call_coroutine (&cr, "2eme appel");
	printf ("2eme appel retourne <%s>\n", x);
	exit(0);
}

/*
main ()
{
	test_coroutine ();
	exit(0);
}
*/



