
#include <setjmp.h>

struct coroutine
{
	jmp_buf *calling;
	jmp_buf *env;
};

void *start_coroutine (struct coroutine *cr,
	void *(*f) (/* void *p, struct coroutine *cr */),
	void *p, int *stack);

void *call_coroutine (struct coroutine *cr, void *entree);

