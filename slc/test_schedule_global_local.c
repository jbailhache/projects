
#include <stdlib.h>
#include <string.h>

#include "schedule.h"

long global;

void *maincr (void *p, struct coroutine *c1)
{
struct coroutine calling[1];
long x;
long local;
	memcpy (calling, c1, sizeof(calling));

	printf("Test\n");
	global = 333;
	local = 444;
	x = (long) alt (calling, (void *)111, (void *)222);
	printf ("x=%ld global=%ld local=%ld\n", x, global, local);	
	if (x == 111) 
	{
		global = 3333;
		local = 4444;
	}
	end (calling);
}

void main ()
{
int stack [8000];
void *maincr ();
struct param_scheduler p;
	p.stack_size = sizeof(stack)-STACK_BOTTOM*sizeof(int);
	scheduler (maincr, &p, stack, p.stack_size, 0);
	printf ("global=%ld\n", global);
}


