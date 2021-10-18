
#include <stdlib.h>
#include <string.h>

#include "schedule.h"

struct coroutine calling[1];

int pof () {
	if (alt (calling, (void *)1, (void *)0)) {
		return 1;
	} else {
		return 0;
	}
}

void *maincr (void *p, struct coroutine *c1)
{
//struct coroutine calling[1];
long x;
long i;
	memcpy (calling, c1, sizeof(calling));

	for (i=1; i<10; i++)
	{
	  if (pof()) {
		printf ("i=%ld\n", i);
		if (i%2 == 0) end(calling);
		x = (long) alt (calling, (void *)(i*10+1), (void *)(i*10+2));
		printf ("x = %ld\n", x);	
		end (calling);
	  }
	}
	
	exit(0);
}

void main ()
{
int stack [8000];
void *maincr ();
struct param_scheduler p;
	p.stack_size = sizeof(stack)-STACK_BOTTOM*sizeof(int);
	scheduler (maincr, &p, stack, p.stack_size, 0);
}


