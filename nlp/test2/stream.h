
typedef struct get_fnct
{
	int (*f) (/* void *p */);
	void *p;
} get_fnct;

typedef struct put_fnct
{
	int (*f) (/* void *p, char c */);
	void *p;
} put_fnct;

#define cget(get) ((*((get)->f))((get)->p))
#define cput(put,c) ((*((put)->f))((put)->p,c))

#include <stdio.h>

// #define int short

struct param_file
{
	FILE *fd;
};

struct param_str
{
	char *s;
};

extern int f_get_file (struct param_file *);
extern int f_put_file (struct param_file *, char);

void sput (struct put_fnct *, char *);

