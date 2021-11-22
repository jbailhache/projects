
#include <stdlib.h>
#include <string.h>

#include "schedule_w64.h"

void *maincr (void *p, struct coroutine *c1)
{
struct coroutine calling[1];
long x;
	memcpy (calling, c1, sizeof(calling));

	printf("Test\n");
	x = (long) alt (calling, (void *)111, (void *)222);
	printf ("x = %ld\n", x);	
	end (calling);
}

void main ()
{
int stack [8000];
void *maincr ();
struct param_scheduler p;
	p.stack_size = sizeof(stack)-STACK_BOTTOM*sizeof(int);
	scheduler (maincr, &p, stack, p.stack_size, 0);
}


