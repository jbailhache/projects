
#include "config.h"

#include <setjmp.h>

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

struct param_scheduler
{
	int stack_size;
};


