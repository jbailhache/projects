
#include "stream.h"

void sput (struct put_fnct *put, char *s)
{
	if (s == NULL)
	    return;
	while (*s)
		cput (put, *s++);
}

void sget (struct get_fnct *get, char *s)
{
int c;
	for (;;)
	{
		c = cget (get);
		if (c == EOF || c == '\n')
			break;
		*s++ = c;
	}
	*s = 0;
}

int f_get_file (struct param_file *p)
{
	return getc (p->fd);
}

int f_put_file (struct param_file *p, char c)
{
	return putc (c, p->fd);
}

int f_get_str (struct param_str *p)
{
	return *((p->s)++);
}

int f_put_str (struct param_str *p, char c)
{
	*((p->s)++) = c;
	return c;
}

