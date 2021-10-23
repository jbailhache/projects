
#include "config.h"

#include <setjmp.h>
#include <malloc.h>

#define STACK_SIZE /* 500 */ 30000
#define STACK_BOTTOM 50

struct coroutine
{
	jmp_buf *calling;
	jmp_buf *env;
};

struct requete
{
	jmp_buf *env;
	int op;
	void *p[5];
};

#define PL_STATUS_ALT 1
#define PL_STATUS_CUT 2

struct process_list
{
	struct process_list *prev, *next, *alt;
	int status;
	int prio;
	jmp_buf env;
	struct requete r;
	int stack_size;
	int stack [STACK_BOTTOM];
};

#define OPT_PRIO 1

struct canal
{
	char flag, prio;
	struct process_list *file;
};

#define end end_cr

void *alt (struct coroutine *calling, void *a, void *b);
void end (struct coroutine *calling);
void print_jmp_buf (jmp_buf env);
void *scheduler (void *(*f) (), void *p, int *astack, int stack_size, int options);

struct param_scheduler
{
	int stack_size;
};


