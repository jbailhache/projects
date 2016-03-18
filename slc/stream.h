
typedef struct get_fnct
{
	int (*f) (/* void *p */);
	void *p;
} get_fnct;

typedef struct put_fnct
{
	void (*f) (/* void *p, char c */);
	void *p;
} put_fnct;

#define cget(get) ((*((get)->f))((get)->p))
#define cput(c,put) ((*((put)->f))((put)->p,c))

#include <stdio.h>

struct param_file
{
	FILE *fd;
};

extern int f_get_file (struct param_file *);
extern int f_put_file (struct param_file *, char);

sput (char *, struct put_fnct *);
