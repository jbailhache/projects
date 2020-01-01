
    #include <stdlib.h>
    #include <setjmp.h>


    static void *coarg;

    void *coto(jmp_buf here, jmp_buf there, void *arg) {
	coarg = arg;
        if (setjmp(here)) return(coarg);
	longjmp(there, 1);
    }


    #define STACKDIR - // set to + for upwards and - for downwards
    #define STACKSIZE (1<<12)

    static char *tos; // top of stack

    void *cogo(jmp_buf here, void (*fun)(void*), void *arg) {
        if (tos == NULL) tos = (char*)&arg;
        tos += STACKDIR STACKSIZE;
        char n[STACKDIR (tos - (char*)&arg)];
        coarg = n; // ensure optimizer keeps n
        if (setjmp(here)) return(coarg);
	fun(arg);
	abort();
    }


    #define MAXTHREAD 10000

    static jmp_buf thread[MAXTHREAD];
    static int count = 0;

    static void comain(void *arg) {
	int *p = arg, i = *p;
	for (;;) {
		printf("coroutine %d at %p arg %p\n", i, (void*)&i, arg);
		int n = rand() % count;
		printf("jumping to %d\n", n);
		arg = coto(thread[i], thread[n], (char*)arg + 1);
	}
    }

    int testfinch(void) {
	while (++count < MAXTHREAD) {
		printf("spawning %d\n", count);
		cogo(thread[0], comain, &count);
	}
	return 0;
    }

int start_coroutine (struct coroutine *cr,
	int (*f) (),
	void *p, int *stack)
{
	cogo(*(cr->calling),f,p); // problems: f different, no result
}

int call_coroutine (struct coroutine *cr, int entree)
{
int x;
	coto(*(cr->calling),*(cr->env),entree); // problem : does not transmit entree to longjmp, no result
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
#define STACK_SIZE 10000
long stack [STACK_SIZE];
int x;
	cr.calling = &calling;
	cr.env = &env;
	x = start_coroutine (&cr, coroutine1, (int)"Parametre lancement",
		stack + STACK_SIZE - 100);
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



