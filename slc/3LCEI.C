
#include <stdio.h>
#include <errno.h>
#include <io.h>
#include <fcntl.h>
#include <dos.h>

#define APSUBST

#define DEM dem

#define _read _read_dem

enum node {
#ifndef APSUBST
	node_ap,
#endif
	node_ap1,
	node_transym, node_ltransym, node_rtransym, node_symbol, node_var, node_lambda,
	node_subst, node_apsubst, node_axiom, node_read,
	node_instr, node_int, node_top, node_left, node_right,
	node_refl, node_Refl };

enum instr {
	instr_node, instr_subdem, instr_eq, instr_posp,
	instr_lr,
	instr_read, instr_print, instr_quote, instr_eval,
	instr_getctx, instr_setctx,
	instr_plus, instr_tplus, instr_minus,
	};

char *code_instr [] = {
	"node", "subdem", "eq", "posp",
	"lr",
	"read", "print", "quote", "eval",
	"getctx", "setctx",
	"plus", "tplus", "minus" };

#ifdef APSUBST
#define node_ap node_apsubst
#endif

typedef struct dem *dem;

struct dem
{
	enum node _node;
	int _level;
	char *_name;
	dem _subdem[2], _lr[2], _value, _red[2], _exec;
	char _buf[10];
};

#define node(d) ((d)->_node)
#define level(d) ((d)->_level)
#define name(d) ((d)->_name)
#define subdem(n,d) ((d)->_subdem[(n)])
#define sd0(d) ((d)->_subdem[0])
#define sd1(d) ((d)->_subdem[1])
#define fnc(d) ((d)->_subdem[0])
#define arg(d) ((d)->_subdem[1])

#define ap(f,a) mkdem (node_ap, 0, NULL, f, a)
#define ap1(f,a) mkdem (node_ap1, 0, NULL, f, a)
#define lambda(a) mkdem (node_lambda, 0, NULL, a, NULL)
#define var(n) mkdem (node_var, n, NULL, NULL, NULL)
#define mksubst(a,b) mkdem (node_subst, 0, NULL, a, b)
#define mkapsubst(a,b) mkdem (node_apsubst, 0, NULL, a, b)

#define mkint(n) mkdem (node_int, n, NULL, NULL, NULL)
#define value(d) ((d)->_level)

#define mktop(d) mkdem (node_top, 0, NULL, d, NULL)

#define MAX_DEMS 500

struct memory
{
	int ndems;
	int max_dems;
	struct dem dems[MAX_DEMS];
} _memory;

typedef struct memory *memory;

int mygetchar1 ()
{
char c;
int status;
/*
	_AH = 1;
	geninterrupt (0x21);
	c = _AL;
	return c;
*/
	status = read (0, &c, 1);
	if (status == 1)
		return c;
	else
		return -1;
}

#define HANDLE

#ifdef FCB
struct myfcb
{
	char lecteur;
	char nom[8];
	char ext[3];
	int bloc;
	int taille_enreg;
	long taille_fichier;
	int date;
	int heure;
	int reserve;
	char nec;
	long ner;

};

movename (char *filename, char *dest)
{
int i;
char *s, *d;
	s = filename;
	d = dest;
	memcpy (dest, "           ", 11);
	for (;;)
	{
		if (*s == 0)
			break;
		if (*s == '.')
		{
			d = dest+8;
			s++;
		}
		else
		{
			*d++ = *s++;
		}
	}
}

int myopen (struct myfcb *fcb, char *filename)
{
int status;
	movename (filename, fcb->nom);
	fcb->taille_enreg = 1;
	_AH = 15;
	_DX = fcb;
	geninterrupt (0x21);
	status = _AL;
	return status;
}

int myclose (struct myfcb *fcb)
{
int status;
	_AH = 16;
	_DX = fcb;
	geninterrupt (0x21);
	status = _AL;
	return status;
}

int myfgetc (struct myfcb *fcb)
{
int c;
int status;
char *adr;
/*
char buf[2048];
	_AH = 0x1A;
	_DX = buf;
	geninterrupt (0x21);
*/
	_AH = 0x14;
	_DX = fcb;
	geninterrupt (0x21);
	status = _AL;
	if (status == 0)
	{
		_AH = 0x2F;
		geninterrupt (0x21);
		adr = _BX;
		return *adr;
	}
	else
		return -1;
}
#endif

#ifdef HANDLE

struct myfcb
{
	int fh;
};

int myopen (struct myfcb *fcb, char *filename)
{
	fcb->fh = open (filename, O_RDONLY);
	return errno;
}

int myclose (struct myfcb *fcb)
{
	close (fcb->fh);
	return errno;
}

int myfgetc (struct myfcb *fcb)
{
char c;
int status;
	status = read (fcb->fh, &c, 1);
	if (status == 1)
		return c;
	else
		return -1;
}




#endif

#ifdef STD

struct myfcb
{
	FILE *f;
};

int myopen (struct myfcb *fcb, char *filename)
{
	fcb->f = fopen (filename, "r");
	return errno;
}

int myclose (struct myfcb *fcb)
{
	fclose (fcb->f);
	return errno;
}

int myfgetc (struct myfcb *fcb)
{
int status;
char c;
	status = fread (&c, 1, 1, fcb->f);
	if (status == 1)
		return c;
	else
		return -1;
}

#endif

/* typedef FILE *desc; */

typedef struct myfcb desc;

desc files[30];

int file_level = 0;

int mygetchar2 ()
{
int c;

debut:
	if (file_level <= 0)
		c = mygetchar1 ();
	else
	{
		c = myfgetc (files+file_level);
		if (c == EOF)
		{
			myclose (files+file_level);
			file_level--;
			goto debut;
		}
	}
	return c;
}

int mygetchar ()
{
char filename[200];
int i;
int c;
FILE *f;
struct myfcb fcb;
int status;

debut:
	c = mygetchar2 ();
	if (c == '"')
	{
		for (i=0; ; i++)
		{
			c = mygetchar2 ();
			if (c == '"')
			{
				filename[i] = 0;
				break;
			}
			filename[i] = c;
		}
		/*
		f = fopen (filename, "r");
		if (f == NULL)
		{
			perror (filename);
		}
		else
		{
			file_level++;
			files[file_level] = f;
		}
		*/
		file_level++;
		/*
		files[file_level].taille_enreg = 1;
		movename (filename, files[file_level].nom);
		*/
		status = myopen (files+file_level, filename);
		if (status)
		{
			perror (filename);
			file_level--;
		}
		goto debut;
	}
	return c;
}

init (memory pm)
{
	pm->ndems = 0;
	pm->max_dems = MAX_DEMS;
}

dem _mkdem (memory pm, enum node node, int level, char *name, dem sd0, dem sd1)
{
int i;
	for (i=0; i<pm->ndems; i++)
	{
		if ((name != NULL) && !strcmp(name,pm->dems[i]._name))
			return pm->dems+i;
		if (pm->dems[i]._node == node &&
		    pm->dems[i]._level == level &&
		    ((node != node_symbol) || (pm->dems[i]._name == name || !strcmp (pm->dems[i]._name, name))) &&
		    pm->dems[i]._subdem[0] == sd0 &&
		    pm->dems[i]._subdem[1] == sd1)
			return pm->dems+i;
	}
	if (pm->ndems >= pm->max_dems)
	{
		printf ("Memory full\n");
		exit (0);
	}
	pm->dems[pm->ndems]._node = node;
	pm->dems[pm->ndems]._level = level;
	if (name == NULL)
	{
		pm->dems[pm->ndems]._name = NULL;
		pm->dems[pm->ndems]._buf[0] = 0;
	}
	else
	{
		strcpy (pm->dems[pm->ndems]._buf, name);
		pm->dems[pm->ndems]._name = pm->dems[pm->ndems]._buf;
	}
	pm->dems[pm->ndems]._subdem[0] = sd0;
	pm->dems[pm->ndems]._subdem[1] = sd1;
	pm->dems[pm->ndems]._lr[0] = NULL;
	pm->dems[pm->ndems]._lr[1] = NULL;
	pm->dems[pm->ndems]._value = NULL;
	pm->dems[pm->ndems]._red[0] = NULL;
	pm->dems[pm->ndems]._red[1] = NULL;
	return pm->dems+pm->ndems++;
}

dem mkdem (enum node node, int level, char *name, dem sd0, dem sd1)
{
dem d1;
	d1 = _mkdem (&_memory, node, level, name, sd0, sd1);
	return d1;
}

#define trace_dem(s,d) /* printf ("trace : %s ", s); printlr (d); printf ("\n"); */

dem shift (int m, int n, dem x)
{
    if (x == NULL)
        return NULL;
    if (node(x) == node_var)
        if (level(x) >= m)
	    return var (level(x)+n);
        else
            return x;
    if (node(x) == node_lambda)
	return lambda (shift (m+1, n, sd0(x)));
    if (node(x) == node_var || node(x) == node_symbol)
	return mkdem (node(x), level(x), name(x),
	       NULL, NULL);
    return mkdem (node(x), level(x), NULL,
	   shift (m, n, sd0(x)),
	   shift (m, n, sd1(x)));
}

dem subst (int n, dem y, dem z);

dem subst1 (int n, dem y, dem z)
{
dem r0, r1, r;
    if (y == NULL)
        return NULL;
    if (node(y) == node_var)
    {
        if (level(y) == n)
        	return z;
	if (level(y) > n)
		return mkdem (node_var, level(y)-1, NULL, NULL, NULL);
    }
    if (node(y) == node_ap)
	return ap (subst (n, sd0(y), z),
		   subst (n, sd1(y), z));
    if (node(y) == node_lambda)
	return lambda (subst (n+1, sd0(y), shift (0, 1, z)));
    /* return y; */
    if (node(y) == node_symbol)
	return y;
    /*
    return mkdem (node(y), level(y), name(y),
			subst (n, sd0(y), z),
			subst (n, sd1(y), z));
    */
    r0 = subst (n, sd0(y), z);
    r1 = subst (n, sd1(y), z);
    r = mkdem (node(y), level(y), NULL /*name(y)*/, r0, r1);
    return r;
}

int level = 0;

dem subst (int n, dem y, dem z)
{
dem r;
int i;
/*
	printf ("%3d: ", level);
	for (i=0; i<level; i++)
		printf (" ");
	printf ("Subst at level %d in ", n);
	printlr (y);
	printf (" by ");
	printlr (z);
	printf ("\n");
	level++;
*/
	r = subst1 (n, y, z);
/*
	level--;
	printf ("%3d: ", level);
	for (i=0; i<level; i++)
		printf (" ");
	printf ("subst at level %d in ", n);
	printlr (y);
	printf (" by ");
	printlr (z);
	printf (" returns ");
	printlr (r);
	printf ("\n");
*/
	return r;
}


dem DBname (int n, dem x, dem y)
{
    if (y == NULL)
        return NULL;
    if (x == y)
	return var(n);
    if (node(y) == node_ap)
	return ap (DBname (n, x, sd0(y)),
		   DBname (n, x, sd1(y)));
    if (node(y) == node_lambda)
	return lambda (DBname (n+1, x, sd0(y)));
    /* return y; */
    return mkdem (node(y), level(y), name(y),
	DBname (n, x, sd0(y)),
	DBname (n, x, sd1(y)));
}

dem vlambda (dem x, dem y)
{
	return lambda (DBname (0, x, y));
}

#if 0
DEM DB_lambda (DEM x, DEM y)
{
    return DBLambda (DBname (0, x, y));
}

DEM dbextens (DEM x, DEM y)
{
    if (node(y) == _ap && subdem(1,y) == x && !in (x, subdem(0,y)))
        return subdem(0,y);
    return lambda (x, y);
}
#endif

#define left(d) lr (0, d)
#define right(d) lr (1, d)

dem _read (memory pm);

dem ext (enum node node, int op, dem d, int r)
{
dem d1;
	switch (node)
	{
		case node_read :
			switch (op)
			{
				case 'lr' :
					if (r == 0)
						d1 = d;
					else
						d1 = _read (&_memory);
					break;
				case 'p' :
					printf ("?");
					break;

			}
			break;
		default:
			d1 =  d;
	}
	return d1;
}

int instr_at_level (dem d, int n, int l, int flag_top)
{
#ifdef TRACEALL
	printf ("instr_at_level ");
	print (d);
	printf (" %d %d \n", n, l);
#endif
	if (l < 0)
		return 0;
	if (l == 0)
	{
		if (flag_top == 0 &&
		    d->_node == node_instr &&
		    d->_level == n) /* d->_level = code instr */
			return 1;
		if (flag_top == 1 &&
		    d->_node == node_top &&
		    d->_subdem[0]->_node == node_instr &&
		    d->_subdem[0]->_level == n)
			return 1;
		else
			return 0;
	}
	return instr_at_level (fnc(d), n, l-1, flag_top);
}

dem lr (int r, dem d);

dem exec_instr (dem d)
{
dem d1;
dem x;
#ifdef TRACEALL
	printf ("exec_instr ");
	print (d);
	printf ("\n");
#endif
	if (d->_exec != NULL)
		return d->_exec;
	d1 = NULL;
	if (node(d) == node_top && node(sd0(d)) == node_ap)
	{
		d1 = ap (mktop(fnc(sd0(d))), arg(sd0(d)));
		return d1;
	}

	if (instr_at_level (d, instr_plus, 3, 0) &&
	    arg(fnc(d))->_node == node_int &&
	    arg(d)->_node == node_int)
	{
		d1 = ap (arg(fnc(fnc(d))), mkint(value(arg(fnc(d)))+value(arg(d))));
	}
	else if (instr_at_level (d, instr_tplus, 3, 1) &&
	    arg(fnc(d))->_node == node_int &&
	    arg(d)->_node == node_int)
	{
		d1 = ap (mktop(arg(fnc(fnc(d)))), mkint(value(arg(fnc(d)))+value(arg(d))));
	}
	else if (instr_at_level (d, instr_minus, 2, 0) &&
		node(arg(d)) == node_int)
	{
		d1 = ap (arg(fnc(d)), mkint(-value(arg(d))));
	}
	else if (instr_at_level (d, instr_node, 2, 0))
	{
		d1 = ap (arg(fnc(d)), mkint(node(arg(d))));
	}
	else if (instr_at_level (d, instr_subdem, 3, 0))
	{
		x = arg(d);
		d1 = ap (arg(fnc(fnc(d))), x->_subdem[value(arg(fnc(d)))]);
	}
	else if (instr_at_level (d, instr_posp, 4, 0) &&
		node(arg(fnc(fnc(d)))) == node_int)
	{
		if (value(arg(fnc(fnc(d)))) >= 0)
			d1 = ap (arg(fnc(fnc(fnc(d)))), arg(fnc(d)));
		else
			d1 = ap (arg(fnc(fnc(fnc(d)))), arg(d));
	}
	else if (instr_at_level (d, instr_eq, 5, 0))
	{
		if (arg(fnc(fnc(fnc(d)))) == arg(fnc(fnc(d))))
			d1 = ap (arg(fnc(fnc(fnc(fnc(d))))), arg(fnc(d)));
		else
			d1 = ap (arg(fnc(fnc(fnc(fnc(d))))), arg(d));
	}
	else if (instr_at_level (d, instr_lr, 3, 0) &&
		node(arg(fnc(d))) == node_int)
	{
		d1 = ap (arg(fnc(fnc(d))), lr (value(arg(fnc(d))), arg(d)));
	}

	else if (instr_at_level (d, instr_read, 1, 1))
	{
		x = _read (&_memory);
		d1 = ap (mktop(arg(d)), x);
	}
	else if (instr_at_level (d, instr_print, 2, 1))
	{
		print (arg(d));
		d1 = mktop (arg(fnc(d)));
	}

	d->_exec = d1;
	return d1;
}

dem lr1 (int r, dem d, int flag_exec);

dem lr (int r, dem d)
{
dem d1;
	d1 = lr1 (r, d, 1);
#ifdef TRACEALL
	if (r == 0)
		printf ("LEFT  ");
	else
		printf ("RIGHT ");
	print (d);
	printf (" = ");
	print (d1);
	printf ("\n");
#endif
	return d1;
}

dem lr_noexec (int r, dem d)
{
dem d1;
	d1 = lr1 (r, d, 0);
	return d1;
}

dem lr1 (int r, dem d, int flag_exec)
{
dem d1, f, a, s0, s1;
	if (d->_lr[r] != NULL)
		return d->_lr[r];
	if (r == 1 && flag_exec)
	{
#ifdef TRACEALL
		printf ("EXEC_INSTR %d ", r);
		print (d);
		printf ("\n");
#endif
		d1 = exec_instr (d);
		if (d1)
			return d1;
	}
	switch (node(d))
	{
#ifndef APSUBST
		case node_ap :
			d1 = mkdem (node_ap, 0, NULL, lr (r, sd0(d)), lr (r, sd1(d)));
			break;
#endif
		case node_ap1 :
			d1 = mkdem (node_ap/*1*/, 0, NULL, lr (r, sd0(d)), lr (r, sd1(d)));
			break;

		case node_transym :
#ifndef APSUBST
			if (lr (0, sd0(d)) == lr (0, sd1(d)))
				d1 = lr (1, d->_subdem[r]);
			else
				d1 = mkdem (node_var, 0, NULL, NULL, NULL);
				/* d1 = lr (r, sd0(d)); */
#else
			if (lr (1, sd0(d)) == lr (1, sd1(d)))
				d1 = lr (0, d->_subdem[r]);
			else
				/* d1 = mkdem (node_var, 0, NULL, NULL, NULL); */
				d1 = d;
#endif
			break;
		case node_ltransym :
			if (lr (0, sd0(d)) == lr (0, sd1(d)))
				d1 = lr (1, d->_subdem[r]);
			else
				/* d1 = mkdem (node_var, 0, NULL, NULL, NULL); */
				d1 = d;
				/* d1 = lr (r, sd0(d)); */
			break;
		case node_rtransym :
			if (lr (1, sd0(d)) == lr (1, sd1(d)))
				d1 = lr (0, d->_subdem[r]);
			else
				/* d1 = mkdem (node_var, 0, NULL, NULL, NULL); */
				d1 = d;
			break;
		case node_symbol :
		case node_var :
		case node_instr :
			d1 = d;
			break;
		case node_lambda :
			/*
			print (d);            	\&<0
			print (sd0(d));         &<0
			print (lr(r,sd0(d)));   0
			*/
			d1 = mkdem (node_lambda, 0, NULL, lr (r, sd0(d)), NULL);
			break;
		case node_subst :
			if (r == 0)
				d1 = mkdem (node_ap, 0, NULL,
					mkdem (node_lambda, 0, NULL, sd0(d), NULL),
					sd1(d));
			else
				d1 = subst (0, sd0(d), sd1(d));
			break;
		case node_apsubst :
			/*
			print (d);
			print (sd0(d));
			print (sd1(d));
			*/
			f = lr (1, sd0(d));
			/* print (f); */
			a = lr (1, sd1(d));
			/* print (a); */
			/*
			if (r == 1)
			{
				d1 = exec_instr (d);
				if (d1)
					break;
			}
			*/
			if (r == 1 && node(f) == node_top && node(sd0(f)) == node_lambda)
				d1 = mktop (subst (0, sd0(sd0(f)), a));
			else if (r == 0 || node(f) != node_lambda)
			{
				s0 = lr (r, sd0(d));
				s1 = lr (r, sd1(d));
				d1 = mkdem (node_ap, 0, NULL, s0, s1);
				/* d1 = mkdem (node_ap, 0, NULL, lr (r, sd0(d)), lr (r, sd1(d))); */
			}
			else
				d1 = subst (0, sd0(f), a);
			break;
		case node_axiom :
			d1 = d->_subdem[r];
			break;
		case node_top :
			d1 = mktop (lr (r, sd0(d)));
			break;

		case node_left :
			if (!r) /* left */
				d1 = mkdem (node_left, 0, NULL, lr(r,sd0(d)), NULL);
			else /* right */
				d1 = lr (0, lr(r,sd0(d)));
			break;
		case node_right :
			if (!r) /* left */
				d1 = mkdem (node_right, 0, NULL, lr(r,sd0(d)), NULL);
			else /* right */
				d1 = lr (1, lr(r,sd0(d)));
			break;

		case node_refl :
			d1 = sd0(d);
			break;
		case node_Refl :
			d1 = lr (r, lr (r, sd0(d)));
			break;

		default :
			/*
			d1 = d;
			*/
			d1 = ext (node(d), 'lr', d, r);
			return d1;
	}
	d->_lr[r] = d1;
	return d1;
}

int atom (dem d)
{
	switch (node(d))
	{
		case node_ap:
			return 0;
		default:
			return 1;
        }
}

dem transym1 (dem ab, dem ac)
{
dem bc;
	bc = mkdem (node_transym, 0, NULL, ab, ac);
	return bc;
}

dem sym (dem ab)
{
#ifndef APSUBST
dem aa, ba;
	aa = left (ab);
	ba = transym1 (ab, aa);
	return ba;
#else
dem bb, ba;
	bb = right (ab);
	ba = transym1 (bb, ab);
#endif
}

dem trans (dem ab, dem bc)
{
#ifndef APSUBST
dem ba, ac;
	ba = sym (ab);
	ac = transym1 (ba, bc);
	return ac;
#else
dem cb, ac;
	cb = sym (bc);
	ac = transym1 (ab, cb);
	return ac;
#endif
}

DEM used = NULL;



dem no_red[60];

int nnr = 0;

int flags = 0;

#define FLAG_RED_LAMBDA 1



DEM red1 (DEM x, int red_arg);

DEM red (DEM x)
{
DEM r;
	r = red1 (x, 1);
	return r;
}

DEM red2 (DEM x, int red_arg);

DEM red1 (DEM x, int red_arg)
{
DEM d;
int i;
    trace_dem ("red1", x);
    if (red_arg != 0 && red_arg != 1)
        printf (" ERROR %d ", red_arg);

    for (i=0; i<nnr; i++)
    {
        /* printf ("i=%d\n", i); */
        trace_dem ("", no_red[i]);
        trace_dem ("", x);
        if (no_red[i] == x)
            return x;
    }
    if (used == NULL && x->_red[red_arg] != NULL)
        return x->_red[red_arg];
    else
    {
	d = red2 (x, red_arg);
	trace_dem ("red1 ", x);
        trace_dem ("red1 returns", d);
        if (used == NULL)
        	x->_red[red_arg] = d;
        return d;
    }
}

DEM red3 (DEM x, int red_arg);

DEM red2 (DEM x, int red_arg)
{
DEM t1, t2, t3, t4;
int i;
    t1 = red3 (x, red_arg);
    trace_dem ("red3 ", x);
    trace_dem (" = ", t1);
    for (;;)
    {
        for (i=0; i<nnr; i++)
	{
            trace_dem ("", no_red[i]);
            trace_dem ("", right(t1));
            if (no_red[i] == right(t1))
                return t1;
        }
	t2 = red3 (right(t1), red_arg);
	trace_dem ("red3 ", right(t1));
	trace_dem (" = ", t2);
        if (left(t2) == right(t2))
                return t1;
	trace_dem ("trans of", t1);
	trace_dem ("and", t2);
	t4 = trans (t1, t2);
	trace_dem ("is", t4);
	if (left(t4) == left(t1))
		t1 = t4;
	else
		return t1;
    }
}

DEM red3 (DEM x, int red_arg)
{
DEM t, t1, t2, t3, t4, t5;
int i;
	trace_dem ("red3", x);
        for (i=0; i<nnr; i++)
        {
            trace_dem ("", no_red[i]);
            trace_dem ("", x);
            if (no_red[i] == x)
                return x;
        }

        if (used != NULL && x == left(used))
            return used;

	if ((flags & FLAG_RED_LAMBDA) && node(x) == node_lambda)
        {
	    t1 = red1 (sd0(x), red_arg);
            trace_dem ("DBLambda", t1);
	    t2 = lambda (t1);
            trace_dem ("DBLambda", t2);
            return t2;
        }
	if (atom(x))
            return x;
	if (node(fnc(x)) == node_lambda)
        {
	    return mksubst (subdem(0,fnc(x)), arg(x));
        }
        if (used == NULL && atom (fnc(x)))
	{
                t1 = fnc(x);
                if (red_arg)
                    t2 = red1 (arg(x), red_arg);
                else
                    t2 = arg(x);
		t = ap (t1, t2);
		return t;
	}
	t1 = red1 (fnc(x), red_arg);
        if (red_arg)
        	t2 = red1 (arg(x), red_arg);
        else
            t2 = arg(x);
	t3 = ap (t1, t2);
	if (left(t3) == right(t3))
		return t3;
	t4 = red1 (right(t3), red_arg);
	if (left(t4) == right(t4))
		return t3;
	t = trans (t3, t4);
	return t;
}

/*
    d : a=b
    red a: a=c
    red b: b=d
    reduc d: c=d
*/
DEM reduc (DEM ab, int red_arg)
{
DEM ac, bd, cb, cd;
    ac = red1 (left(ab), red_arg);
    bd = red1 (right(ab), red_arg);
    cb = transym1 (ac, ab);
    cd = trans (cb, bd);
    return cd;
}

#if 0
DEM redu1 (DEM x);

DEM redu (DEM x)
{
int forme_Sfg;
DEM rf, ra, f1, a1, x1, r1, r2, t1, t2, t3, t4, t5, t6, r, rr1;
	trace_dem ("redu", x);
	if (atom(x))
        {
                trace_dem ("atom: return", x);
		return x;
        }
        trace_dem ("not atom", x);
        rf = redu (fnc(x)); trace_dem ("", rf);
        ra = redu (arg(x)); trace_dem ("", ra);
	f1 = right (rf); trace_dem ("", f1);
	a1 = right (ra); trace_dem ("", a1);
        trace_dem ("", x);
        if (fnc(x)==f1 && arg(x)==a1)
	{
		r1 = redu1 (x); trace_dem ("", r1);
                rr1 = right(r1); trace_dem ("", rr1);
		if (rr1 == x)
                {
                        trace_dem ("return", r1);
			return r1;
                }
                trace_dem ("", rr1);
		r2 = redu (rr1); trace_dem ("", r2);
		if (left(r2) == right(r2))
			return r1;
		if (left(r1) == right(r1))
			return r2;
		r = trans (r1, r2); trace_dem ("", r);
		return r;
	}
	x1 = ap (f1, a1); trace_dem ("", x1);
	r1 = redu1 (x1); trace_dem ("", r1);
	if (right(r1) == x)
		r2 = r1;
	r2 = redu (right(r1)); trace_dem ("", r2);
	t3 = ap (rf, ra); trace_dem ("", t3);
	t4 = trans (t3, r1); trace_dem ("", t4);
	t5 = trans (t4, r2); trace_dem ("", t5);
	return t5;
}

DEM redu1 (DEM x)
{
DEM t1, t2, t3, t4, t5, t6, t7, t8, a1, a2;
int forme_SKfg;
        trace_dem ("redu1", x);
        a1 = Ext4;
        a2 = Ext5;
        forme_SKfg = !atom(x) && !atom(fnc(x))
                        && fnc(fnc(x))==S
                        && !atom(arg(fnc(x)))
                        && fnc(arg(fnc(x)))==K;
        if (forme_SKfg && arg(x)==I)
	{
	/* S(Kf)I = I */
                trace_dem ("S(Kf)I", x);
                t1 = arg(arg(fnc(x)));  trace_dem ("", t1);
                t2 = ap (a1, t1);       trace_dem ("", t2);
                t3 = defI (t1);         trace_dem ("", t3);
                t4 = trans (t2, t3);    trace_dem ("", t4);
                t5 = red (left(t4));    trace_dem ("", t5);
                t7 = transym1 (t5, t4);  trace_dem ("", t7);
		return t7;
	}
        if (forme_SKfg && !atom(arg(x)) && fnc(arg(x))==K)
	{
	/* S(Kf)(Ka) = K(fa) */
                trace_dem ("S(Kf)(Ka)", x);
                t1 = arg(arg(fnc(x)));  /* trace_dem ("", t1); */
                t2 = arg(arg(x));       /* trace_dem ("", t2); */
                t3 = app(a2, t1, t2);   /* trace_dem ("", t3); */
                t4 = red (left(t3));    /* trace_dem ("", t4); */
                t6 = transym1 (t4, t3);  /* trace_dem ("", t6); */
                t7 = red (right(t3));   /* trace_dem ("", t6); */
                t8 = trans (t6, t7);    /* trace_dem ("", t8); */
		return t8;
	}
	return x;
}

#endif

dem loop_right (dem d)
{
dem d1;
    for (;;)
    {
#ifdef TRACEALL
	printf ("STEP: ");
	print (d);
	printf ("\n");
#endif
	d1 = right (d);
	if (d1 == d)
		return d;
	d = d1;
    }
}

dem _read (memory pm)
{
int c;
dem sd0, sd1, d;
enum node node;
char buf[30];
int i;
dem used1;

debut:
	/* c = getchar (); */
	/* c = fgetc (stdin); */
	c = mygetchar ();
/*
	pm = &_memory;
	_memory.max_dems = MAX_DEMS;
*/
	switch (c)
	{
		case '.':
			exit (0);
		case '-':
			node = node_ap;
		read01:
			sd0 = _read (pm);
			sd1 = _read (pm);
			d = _mkdem (pm, node, 0, NULL, sd0, sd1);
			break;
		case '/':
			c = mygetchar ();
			switch (c)
			{
				case '/':
					node = node_transym;
					goto read01;
				case '<':
					node = node_ltransym;
					goto read01;
				case '>':
					node = node_rtransym;
					goto read01;
				default:
					node = node_transym;
					goto read01;
			}
		case '%':
			node = node_subst;
			goto read01;
		case '_':
			node = node_apsubst;
			goto read01;
		case '#':
			node = node_axiom;
			goto read01;
		case '!':
			sd0 = _read (pm);
			d = _mkdem (pm, node_top, 0, NULL, sd0, NULL);
			break;
		case '\\':
			sd0 = _read (pm);
			d = _mkdem (pm, node_lambda, 0, NULL, sd0, NULL);
			break;
		case '^' :
			sd0 = _read (pm);
			sd1 = _read (pm);
			d = vlambda (sd0, sd1);
			break;
		case ' ' :
		case '\t' :
		case '\n' :
		case '\r' :
		case 0 :
			goto debut;
		case ':' :
			sd0 = _read (pm);
			sd1 = _read (pm);
			sd0->_value = sd1;
			sd1->_name = sd0->_name;
			d = sd1;
			break;
		case '<' :
			sd0 = _read (pm);
			d = lr (0, sd0);
			break;
		case '>' :
			sd0 = _read (pm);
			d = lr (1, sd0);
			break;
		case '$' :
			sd0 = _read (pm);
			d = red (sd0);
			break;
		case '@' :
			sd0 = _read (pm);
			d = reduc (sd0, 1);
			break;
		case '`':
			used1 = used;
			used = _read (pm);
			d = _read (pm);
			used = used1;
			break;
		case '?':
			d = _mkdem (pm, node_read, 0, NULL, NULL, NULL);
			break;
		case '&':
			c = mygetchar ();
			switch (c)
			{
				case 'N':
					c = mygetchar ();
					d = _mkdem (pm, node_int, c-'0', NULL, NULL, NULL);
					break;
				case '*':
					sd0 = _read (pm);
					d = loop_right (sd0);
					break;
				case '-':
					node = node_ap1;
					goto read01;
				case '<':
					sd0 = _read (pm);
					d = _mkdem (pm, node_left, 0, NULL, sd0, NULL);
					break;
				case '>':
					sd0 = _read (pm);
					d = _mkdem (pm, node_right, 0, NULL, sd0, NULL);
					break;
				case 'r':
					sd0 = _read (pm);
					d = _mkdem (pm, node_refl, 0, NULL, sd0, NULL);
					break;
				case 'R':
					sd0 = _read (pm);
					d = _mkdem (pm, node_Refl, 0, NULL, sd0, NULL);
					break;

				default :
					buf[0] = c;
					for (i=1; ; i++)
					{
						c = mygetchar ();
						if (c == ' ' || c == '\t' || c == '\n' || c == '\r')
						{
							buf[i] = 0;
							break;
						}
						buf[i] = c;
					}
					d = NULL;
					for (i=0; i<sizeof(code_instr)/sizeof(code_instr[0]); i++)
					{
						if (!strcmp (code_instr[i], buf))
						{
							d = _mkdem (pm, node_instr, i, NULL, NULL, NULL);
							break;
						}
					}
			}
			break;
		default :
			if ((c >= '0') && (c <= '9'))
				d = _mkdem (pm, node_var, c-'0', NULL, NULL, NULL);
			else
			{
				buf[0] = c;
				for (i=1; ; i++)
				{
					c = mygetchar ();
					if (c == ' ' || c == '\t' || c == '\n' || c == '\r')
					{
						buf[i] = 0;
						break;
					}
					buf[i] = c;
				}
				/*buf[1] = 0;*/
				d = _mkdem (pm, node_symbol, 0, buf, NULL, NULL);
				if (d->_value != NULL)
					d = d->_value;
			}
	}
	return d;
}


print (dem d)
{
	if (d == NULL)
	{
		printf ("<NULL>");
		return;
	}
	if (d->_name != NULL)
	{
		printf ("%s ", d->_name);
		return;
		/* printf ("[%s]", d->_name); */
	}
	switch (node(d))
	{
		case node_ap :
			printf ("-");
		sd01:
			print (sd0(d));
			print (sd1(d));
			break;
		case node_ap1 :
			printf ("&-");
			goto sd01;
		case node_transym :
			printf ("//");
			goto sd01;
		case node_ltransym :
			printf ("/<");
			goto sd01;
		case node_rtransym :
			printf ("/>");
			goto sd01;

		case node_symbol :
			printf ("%s ", d->_name);
			break;

		case node_var :
			printf ("%d ", d->_level);
			break;

		case node_lambda :
			printf ("\\");
			print (sd0(d));
			break;

		case node_top :
			printf ("!");
			print (sd0(d));
			break;

		case node_subst :
			printf ("%");
			goto sd01;
#ifndef APSUBST /* bizarre mais c'est bien ca */
		case node_apsubst :
			printf ("_");
			goto sd01;
#endif
		case node_axiom :
			printf ("#");
			goto sd01;

		case node_int :
			printf ("&N%c ", '0' + d->_level);
			break;

		case node_instr :
			printf ("&%s ", code_instr [d->_level]);
			break;

		case node_left :
			printf ("&<");
			print (sd0(d));
			break;
		case node_right :
			printf ("&>");
			print (sd0(d));
			break;
		case node_refl :
			printf ("&r");
			print (sd0(d));
			break;
		case node_Refl :
			printf ("&R");
			print (sd0(d));
			break;

		default :
			/*
			printf ("?%d,", node(d));
			goto sd01;
			*/
			ext (node(d), 'p', d, 0);
	}
}

printlr (dem x)
{
	printf (" ");
	print (x);
	printf (" : ");
	print (left(x));
	printf (" = ");
	print (right(x));
	printf (" ");
}

main ()
{
dem d, l, r;
char c;
	/* read (0, &c, 1); */
	printf ("%x %x %x\n", _read, &_memory, MAX_DEMS);
	init (&_memory);
	for (;;)
	{
		printf ("\n? ");
		d = _read (&_memory);
		printf ("\n");
		printlr (d);
		/*
		printf ("\n  ");
		print (d);
		l = lr (0, d);
		printf ("\n");
		print (l);
		printf (" = ");
		r = lr (1, d);
		print (r);
		*/
	}
}



/*
main ()
{
int c;
	for (;;)
	{
		c = getchar ();
		if (c == EOF)
			break;
		putchar (c);
	}
}
*/

/* exemples :
 &* ---&plus \---&plus stop 0 0 &N1 &N2
 -stop &N6 : -stop &N6 = -stop &N6

:quote \\-01
:B \\\-2-10

:prog1
	--B -quote TapezExpr
	--B &print
	--B &read
	--B -quote ExprTapee
	--B &print
	--B &print
	\0

 :transym \\ / 1 0
 :t1 # a c
 :t2 # b c
 &* --transym # t1 t1 # t2 t2

 */




