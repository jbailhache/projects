
#include <setjmp.h>

struct coroutine
{
	jmp_buf *calling;
	jmp_buf *env;
};

