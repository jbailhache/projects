
#include "stream.h"

sput (char *s, struct put_fnct *put)
{
	while (*s)
		cput (*s++, put);
}

int f_get_file (struct param_file *p)
{
	return getc (p->fd);
}

int f_put_file (struct param_file *p, char c)
{
	return putc (c, p->fd);
}
