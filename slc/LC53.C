/* Expressions symboliques LC */

/* compiler en modele memoire Huge */

/* Representation :
	application = indice tableau de paires
	atome : negatif
*/

/* extern int cdecl putchar (char); */
#include <stdio.h>
#include <conio.h>
#include <dos.h>

/* #define ALLOC */

long trace = 0;

#define trace flags

long flags;
#define FLAG_VERBOSE 4
#define FLAG_CH_AP 0x10
#define FLAG_CH_T_AP 0x20
#define FLAG_REDU_TRANS 0x40
#define FLAG_COMPTEUR 0x100
#define FLAG_TRACE 0x1000

#ifdef ALLOC
#define NPAIRES 6000 /* 8000 */
#else
#define NPAIRES 2000 /*3000*/
#endif
#define NPREMISSES 4 /*6*/
#ifdef ALLOC
#define NTHEOREMES 30000 /* 32000 */
#else
#define NTHEOREMES 3000	/* 500 */
#endif


typedef short expr;

struct paire {expr f, a;};

struct paire paires[NPAIRES];
int libre;

#define atom(x) ((x)<0)
#define pairp(x) ((x)>=0)
#define fnc(x) (paires[x].f)
#define arg(x) (paires[x].a)
#define sym(s) ((short)(*(short *)(s) | (short)0x8000))
#define sym1(c) ((c) | 0x8000)

#define I sym1('I')
#define K sym1('K')
#define S sym1('S')
#define _1 sym1('1')
#define N sym1('N')
#define E_aff sym1('!')
#define E_int sym1('?')

#define LAMBDA sym1('^')

#define r_axiom		'A'
#define r_sym           's'
#define r_trans         't'
#define r_ap		'a'
#define r_I		'I'
#define r_K             'K'
#define r_S		'S'
#define r_subst 	'^'
#define r_1		'1'
#define r_N		'N'
#define r_invalid	'?'

/* #define theoremes (far *p_theoremes) */

struct s_theoreme
{
	char regle, n_premisses;
	int premisses[NPREMISSES];
	expr gauche, droite;
}
#ifdef ALLOC
/* far (*p_theoremes)[NTHEOREMES]; */
(huge *p_theoremes)[1];
#else
theoremes[NTHEOREMES];
#endif

int derth;

#ifdef ALLOC
#define theoremes (*p_theoremes)
#endif

int ptr_th;

typedef int theoreme;

#define mg(t) (theoremes[t].gauche)
#define md(t) (theoremes[t].droite)

FILE *entree, *sortie;

#define TAILLE_NOM 7
#define TAILLE_ROUTINE 55
#define NROUTINES 32

struct s_routine
{
	char nom[TAILLE_NOM+1];
	struct s_instr
	{
		char op;
		char ar; /* arg */
	} instr[TAILLE_ROUTINE+1];
} routines[NROUTINES];

int n_routines;


#define c_emp 'T'
#define c_des '['
#define c_mon ']'
#define c_dep 'D'
#define c_rep 'R'
#define c_ech 'X'

#define c_apr 'r'
#define c_cal '<'
#define c_ret 1

#define c_wrt '@'

#define c_udf -1


#define fin_nom '>'

#define tr(t) ((trace&8) ? \
    (indent (), \
     printf ("tr %s(%d) %s: ", __FILE__, __LINE__, #t), \
     print_theorem(t)) \
	 : t)

#define tp(t) if (t <= 0) t = pile[bas-t]

int niveau;

break_debug ()
{
	;
}

int num_routine (char *nom)
{
int i;
	for (i=0; i<n_routines; i++)
		if (!strncmp (nom, routines[i].nom, TAILLE_NOM))
			return i;
	if (n_routines >= NROUTINES)
	{
		printf ("Erreur: debordement de la table des routines\n");
		return -1;
	}
	strncpy (routines[n_routines].nom, nom, TAILLE_NOM);
	routines[n_routines].instr[0].op = c_udf;

	n_routines++;
	return n_routines-1;
}

coder (struct s_instr *obj, char *source)
{
char nom[TAILLE_NOM+1];
int i;
int n;
	n = 0;
	while (*source)
	{
		while (*source == ' ' || *source == '\t')
			source++;
		/*s_instr*/obj->op = *source++;
		if (obj->op == c_emp)
		{
			source += sscanf (source, "%d", &i);
			obj->ar = i;
		}
		if (obj->op == c_apr)
			obj->ar = *source++;
		else if (obj->op == c_cal)
		{
			i = 0;
			while (*source != fin_nom /*&& i<TAILLE_NOM*/)
			{
				if (i < TAILLE_NOM)
					nom[i++] = *source++;
			}
			if (i < TAILLE_NOM)
				nom[i] = 0;
			else
				nom[TAILLE_NOM] = 0;
			obj->ar = num_routine (nom);
		}
		obj++;
		if (n >= TAILLE_ROUTINE - 1)
		{
			printf ("Erreur: debordement routine\n");
			break;
		}
		n++;
	}
	obj->op = c_ret;

}

#define TAILLE_PILE 128
theoreme pile[TAILLE_PILE];

int bas, haut;

theoreme top (int n)
{
	return pile[bas+n];
}

i_emp (theoreme t)
{
	if (bas <= haut+1)
		 printf ("Erreur: debordement de pile\n");
	else
	{
		bas--;
		pile[bas] = t;
	}
}

theoreme i_dep ()
{
	if (bas >= TAILLE_PILE-1)
	{
		printf ("Erreur: pile vide\n");
		return -1;
	}
	else
	{
		bas++;
		return pile[bas];
	}
}

i_rep ()
{
	if (bas <= haut+1)
		 printf ("Erreur: debordement de pile\n");
	else
	{
		bas--;
		pile[bas] = pile[bas+1];
	}
}

i_ech ()
{
theoreme t;
	t = pile[bas];
	pile[bas] = pile[bas+1];
	pile[bas+1] = t;
}

i_des ()
{
	if (bas >= TAILLE_PILE-1)
	{
		printf ("Erreur: pile vide\n");
	}
	else
	{
		haut++;
		pile[haut] = pile[bas];
		bas++;
	}
}

i_mon ()
{
	if (haut < 0)
		printf ("Erreur: pile superieure vide\n");
	else
	{
		bas--;
		pile[bas] = pile[haut];
		haut--;
	}
}

i_apr (char r)
{
theoreme premisses[NPREMISSES];
int n, i;
	n = arite(r);
	if (n < 0)
	{
		printf ("Erreur: regle '%c' 0x%02X non definie\n");
		return;
	}
	if (bas + n > TAILLE_PILE)
	{
		printf ("Erreur dans regle %c: pile vide \n", r);
		return;
	}
	/*
	while (theoremes[ptr_th].regle)
	{
		if (ptr_th <= 0)
		{
			printf ("Erreur: debordement table des theoremes\n");
			return;
		}
		ptr_th--;
	}
	*/
	if (new_th() == -1) return;
	for (i=1; i<=n; i++)
		premisses[i] = pile[bas+i-1];
	dem (ptr_th, r, premisses);
	bas += n-1;
	pile[bas] = ptr_th;

}

interp (int nr)
{
int ip;
struct s_instr *prog;

	prog = routines[nr].instr;
	/* ip = 0; */
	for (ip=0; ip<TAILLE_ROUTINE; ip++)
	{
		switch (prog[ip].op)
		{
			case c_emp: i_emp (prog[ip].ar); break;
			case c_dep: i_dep(); break;
			case c_rep: i_rep(); break;
			case c_ech: i_ech(); break;
			case c_mon: i_mon(); break;
			case c_des: i_des(); break;
			case c_wrt: print_theorem (pile[bas]); break;
			case c_apr: i_apr (prog[ip].ar); break;
			case c_cal: interp (prog[ip].ar);
			case c_ret: return;
			case c_udf: printf ("Routine <%s> non definie\n",
						routines[nr].nom);
				    return;
			default: printf (
	"Instruction %c (0x%02X) non definie dans la routine <%s>\n",
					prog[ip].op, prog[ip].op,
					routines[nr].nom);
				 return;
		}
	}
}

alloc_theoremes ()
{
#ifdef ALLOC
union REGS reg;
	reg.x.bx = NTHEOREMES * sizeof(struct s_theoreme) / 16 + 1;
	reg.h.ah = 0x48;
	intdos (&reg, &reg);
	if (reg.x.flags & 1)
		printf ("Erreur allocation 0x%X %d\n", reg.x.ax, reg.x.bx);
	printf ("Table des theoremes allouee, segment 0x%X\n",
		reg.x.ax);
	p_theoremes = MK_FP (0x1234, 0x5678);
	p_theoremes = MK_FP (reg.x.ax, 0);
#endif
}

init ()
{
int i;
	libre = 0;
	derth = -1;
	/* ptr_th = NTHEOREMES - 1; */
	ptr_th = 501;
	entree = stdin;
	sortie = stdout;
	alloc_theoremes ();
	for (i=0; i<NTHEOREMES; i++)
		theoremes[i].regle = 0;
	bas = TAILLE_PILE;
	haut = -1;
	n_routines = 1;
	flags = FLAG_VERBOSE | FLAG_CH_AP | FLAG_CH_T_AP | FLAG_REDU_TRANS;
	niveau = 0;
}

expr ap (f, a) expr f, a;
{
int r;
int i;
	if (flags & FLAG_CH_AP)
	{
		for (i=0; i<libre; i++)
			if (paires[i].f == f && paires[i].a == a)
				return i;
	}
	if (libre >= NPAIRES)
	{
		printf ("Debordement de la table des expressions\n");
		print_theorems ();
		exit (-1);
	}
	paires[libre].f = f;
	paires[libre].a = a;
	r = libre;
	libre++;
	return r;
}

#define printchar(c) putc (c, sortie)

printexpr (expr x)
{
	if (atom(x))
	{
		printchar (x & 0xFF);
		printchar ((x >> 8) & 0x7F);
		return;
	}
	printchar ('(');
	printexpr (fnc(x));
	printchar (' ');
	printexpr (arg(x));
	printchar (')');
}

pfrexpr (expr x)
{
	if (atom(x))
	{
		printchar (x & 0xFF);
		/* printchar ((x >> 8) & 0x7F); */
		return;
	}
	printchar ('-');
	pfrexpr (fnc(x));
	pfrexpr (arg(x));
}

#define readchar getc(entree)

int occ (expr x, expr r)
{
	if (x == r)
		return 1;
	if (atom(r))
		return 0;
	if (occ(x,fnc(r))
	)	return 1;
	if (occ(x,arg(r)))
		return 1;
	return 0;
}

expr abstract (expr x, expr r)
{
	if (trace & 1)
		printf ("{abstract 0x%X 0x%X}", x, r);

	if (x == r)
		return I;
	if (!occ(x,r))
		return ap (K, r);
	if (atom(r))
{
		printf ("Erreur abstract\n");
		return -1;
	}
	if (x == arg(r) && !occ(x,fnc(r)))
		return fnc(r);
	return ap (ap (S, abstract(x,fnc(r))), abstract(x,arg(r)));
}


expr readexpr()
{
expr f, a;
char c;
int n;
	do c=readchar;
/*
	while (!(c=='-' || (c>='A' && c<='Z') || (c>='a' && c<='z') ||
		(c>='0' && c<='9')));
*/
	while (c==' ' || c=='\t' || c=='\n' || c==0);
	if (c != '-' && c != '\\' && c != '<' && c != '>' && c != '%')
	       return sym1(c);
	if (c == '\\')
	{
		c = readchar;
		return abstract (sym1(c), readexpr());
	}
	if (c == '<')
	{
		fscanf (entree, "%d", &n);
		tp (n);
		return theoremes[n].gauche;
	}
	if (c == '>')
	{
		fscanf (entree, "%d", &n);
		tp (n);
		return theoremes[n].droite;
	}
	if (c == '%')
	{
		c = getc(entree);
		switch (c)
		{
			case 'f':
				return fnc(readexpr());
			case 'a':
				return arg(readexpr());
			default:
				printf ("Erreur syntaxique\n");
				return readexpr();
		}
	}
	f = readexpr();
	a = readexpr();
	return ap (f, a);
}

readeq (expr *x, expr *y)
{
char k;
expr a, b, c, d;
expr v;

	do k = getc (entree);
	while (k==' ' || k=='\t');
	switch (k)
	{
		case '=':
			*x = readexpr();
			*y = readexpr();
			break;
		case '!':
			readeq (&a, &b);
			readeq (&c, &d);
			*x = ap (ap (ap (E_aff, a), b), c);
			*y = ap (ap (ap (E_aff, a), b), d);
			break;
		case '?':
			readeq (&a, &b);
			readeq (&c, &d);
			*x = ap (ap (ap (E_int, a), b), c);
			*y = ap (ap (ap (E_int, a), b), d);
			break;
		case '\\':
			k = getc(entree);
			v = sym1(k);

			readeq (&a, &b);
			*x = abstract (v, a);
			*y = abstract (v, b);
			break;
		case '^':
			k = getc(entree);
			v = sym1(k);
			readeq (&a, &b);
			*x = ap (ap (LAMBDA, v), a);
			*y = ap (ap (LAMBDA, v), b);
			break;
		default:
			printf ("Erreur syntaxique: '%c'\n", k);
	}
}


#define I sym("I")
#define K sym("K")
#define S sym("S")

#define LAMBDA sym("^")

int equal (x, y) expr x, y;
{
	if (x == y)
		return 1;
	if (atom(x))
	{
		if (atom(y)) return x == y;
		return 0;
	}
	if (atom(y)) return 0;
	return equal (fnc(x), fnc(y)) && equal (arg(x), arg(y));
}

/* lambda x y a = substitution de x dans y par a */

expr subst (expr x, expr y, expr a)
{
	if (y == x)
		return a;
	if (atom(y))
		return y;
	if (!atom(fnc(y)) && fnc(fnc(y)) == LAMBDA && arg(fnc(y)) == x)
		return y;
	return ap (subst (x, fnc(y), a), subst (x, arg(y), a));
}

#define vt(t) \
	if (theoremes[t].regle == 0) \
	{ \
		break_debug (); \
		printf ("*** Theoreme %d invalide\n", t); \
		while (!kbhit()); \
		return; \
	}

d_axiom (t, a, b)  theoreme t; expr a,b;
{
	theoremes[t].regle = r_axiom;
	theoremes[t].n_premisses = 0;
	theoremes[t].gauche = a;
	theoremes[t].droite = b;
}

theoreme t_axiom (a, b) expr a, b;
{
	derth++;
	d_axiom (derth, a, b);
	return derth;
}

d_sym (t, t1) theoreme t, t1;
{
	vt(t1)
	theoremes[t].regle = r_sym;
	theoremes[t].n_premisses = 1;
	theoremes[t].premisses[1] = t1;
	theoremes[t].gauche = theoremes[t1].droite;
	theoremes[t].droite = theoremes[t1].gauche;
}

/*
t_sym (t1) theoreme t1;
{
	derth++;
	d_sym (derth, t1);
	return derth;
}
*/

#if 0
#define def_t1(t,d) \
theoreme t (t1) theoreme t1; \
{ \
	derth++; \
	d (derth, t1); \
	return derth; \
}
#endif

#define def_t1(t,d) \
theoreme t (t1) theoreme t1; \
{ \
theoreme r; \
	r = new_th(); \
	if (r == -1) return -1; \
	d (r, t1); \
	return r; \
}

#define def_t2(t,d) \
theoreme t (t1, t2) theoreme t1, t2; \
{ \
theoreme r; \
	r = new_th(); \
	if (r == -1) return -1; \
	d (r, t1, t2); \
	return r; \
}

#define def_t3(t,d) \
theoreme t (t1, t2, t3) theoreme t1, t2, t3; \
{ \
theoreme r; \
	r = new_th(); \
	if (r == -1) return -1; \
	d (r, t1, t2, t3); \
	return r; \
}

def_t1 (t_sym, d_sym)

compteur ()
{
	if (flags & FLAG_COMPTEUR)
		printf ("\r %d \t %d ", ptr_th, libre);
}

d_trans (t, t1, t2)
{
	vt(t1) vt(t2)
	compteur ();
	if (equal (theoremes[t1].droite, theoremes[t2].gauche))
	{
		theoremes[t].regle = r_trans;
		theoremes[t].n_premisses = 2;
		theoremes[t].premisses[1] = t1;
		theoremes[t].premisses[2] = t2;
		theoremes[t].gauche = theoremes[t1].gauche;
		theoremes[t].droite = theoremes[t2].droite;
		return 1;
	}
	else
	{
	    /*if (!(flags & FLAG_REDU_TRANS))
	    {*/
		fprintf (sortie, "%d: transitivite inapplicable\n");
		fprintf (sortie, "\t%d: ", t1);
		/*printexpr*/ pfrexpr (theoremes[t1].gauche);
		fprintf (sortie, " = ");
		pfrexpr (theoremes[t1].droite);
		fprintf (sortie, "\n\t%d: ", t2);
		pfrexpr (theoremes[t2].gauche);
		fprintf (sortie, " = ");
		pfrexpr (theoremes[t2].droite);
		fprintf (sortie, "\n");
		while (!kbhit());
	    /*}*/
		theoremes[t].regle = r_invalid;
		theoremes[t].n_premisses =0;
		theoremes[t].gauche = I;
		theoremes[t].droite = I;
		return 0;
	}
}

/*
t_trans (t1, t2) theoreme t1, t2;
{
	derth++;
	d_trans (derth, t1, t2);
	return derth;
}
*/
def_t2 (t_trans1, d_trans);

theoreme ax_1, ax_2;

theoreme t_trans2 (t1, t2) theoreme t1, t2;
{
	tr (t1);
	tr (t2);
	if (equal (md(t1), mg(t2)))
	{
		tr (t1);
		tr (t2);
		return t_trans1 (t1, t2);
	}
	if (equal (mg(t1), mg(t2)))
	{
		tr (t1);
		tr (t2);
		return t2;
	}
	if (equal (md(t1), md(t2)))
	{
		tr (t1);
		tr (t2);
		return t1;
	}
	tr (t1);
	tr (t2);
	return t_trans1 (t1, t2);
}

theoreme reduc (expr x, theoreme ax1, theoreme ax2)
{
theoreme t1, t2, t3;
	t1 = red (x);
	tr (t1);
	t2 = redu (md(t1), ax1, ax2);
	tr (t2);
	t3 = t_transit (t1, t2);
	tr (t3);
	return t3;
}

theoreme t_trans (t1, t2) theoreme t1, t2;
{
theoreme t, t3, t4, t5, t6, t7, t8;
	tr (t1);
	tr (t2);
	vt (t1)
	vt (t2)
	if (!(flags & FLAG_REDU_TRANS))
		return t_trans1 (t1, t2);
	if (equal (md(t1), mg(t2)))
		return t_trans1 (t1, t2);
	t3 = reduc (md(t1), ax_1, ax_2);
	tr (t3);
	if (equal (md(t3), mg(t2)))
	{
		t4 = t_trans2 (t1, t3);
		tr (t4);
		t5 = t_trans2 (t4, t2);
		tr (t5);
		return t5;
	}
	t4 = reduc (mg(t2), ax_1, ax_2);
	if (equal (md(t4), md(t1)))
	{
		t5 = t_sym (t4);
		tr (t5);
		t6 = t_trans2 (t1, t5);
		tr (t6);
		t7 = t_trans2 (t6, t2);
		tr (t7);
		return t7;
	}
	tr (t4);
	t5 = t_trans2 (t1, t3);
	tr (t5);
	t6 = t_sym (t4);
	tr (t6);
	t7 = t_trans2 (t5, t6);
	tr (t7);
	tr (t2);
	t8 = t_trans2 (t7, t2);
	tr (t8);
	return t8;
}

d_ap (t, t1, t2) theoreme t, t1, t2;
{
	vt(t1) vt(t2)
	theoremes[t].regle = r_ap;
	theoremes[t].n_premisses = 2;
	theoremes[t].premisses[1] = t1;
	theoremes[t].premisses[2] = t2;
	theoremes[t].gauche = ap (theoremes[t1].gauche,
				  theoremes[t2].gauche);
	theoremes[t].droite = ap (theoremes[t1].droite,
				  theoremes[t2].droite);
}

def_t2 (t_ap1, d_ap)

t_ap (t1, t2) theoreme t1, t2;
{
expr f, g, a, b, fa, gb;
theoreme ch;
	if (!(flags & FLAG_CH_T_AP))
		return t_ap1 (t1, t2);
	f = mg(t1);
	g = md(t1);
	a = mg(t2);
	b = md(t2);
	fa = ap (f, a);
	gb = ap (g, b);
	ch = chercher (fa, gb);
	if (ch > 0)
		return ch;
	return t_ap1 (t1, t2);
}

d_I (t, t1) theoreme t, t1;
{
	vt(t1)
	theoremes[t].regle = r_I;
	theoremes[t].n_premisses = 1;
	theoremes[t].premisses[1] = t1;
	theoremes[t].gauche = ap (I, theoremes[t1].gauche);
	theoremes[t].droite = theoremes[t1].droite;
}

def_t1 (t_I, d_I)

d_K (t, t1, t2) theoreme t, t1, t2;
{
	vt(t1) vt(t2)
	theoremes[t].regle = r_K;
	theoremes[t].n_premisses = 2;
	theoremes[t].premisses[1] = t1;
	theoremes[t].premisses[2] = t2;
	theoremes[t].gauche = ap (ap (K, theoremes[t1].gauche),
					theoremes[t2].gauche);
	theoremes[t].droite = theoremes[t1].droite;
}

def_t2 (t_K, d_K)

d_S (t, t1, t2, t3) theoreme t, t1, t2, t3;
{
	vt(t1) vt(t2) vt(t3)
	theoremes[t].regle = r_S;
	theoremes[t].n_premisses = 3;
	theoremes[t].premisses[1] = t1;
	theoremes[t].premisses[2] = t2;
	theoremes[t].premisses[3] = t3;
	theoremes[t].gauche = ap (ap (ap (S, theoremes[t1].gauche),
					theoremes[t2].gauche),
				     theoremes[t3].gauche);
	theoremes[t].droite = ap (ap (theoremes[t1].droite,
				      theoremes[t3].droite),
				  ap (theoremes[t2].droite,
				      theoremes[t3].droite));
}

def_t3 (t_S, d_S)

d_subst (t, t1, t2, t3) theoreme t, t1, t2, t3;
{
	vt(t1) vt(t2) vt(t3)
	theoremes[t].regle = r_subst;
	theoremes[t].n_premisses = 3;
	theoremes[t].premisses[1] = t1;
	theoremes[t].premisses[2] = t2;
	theoremes[t].premisses[3] = t3;
	theoremes[t].gauche = ap (ap (ap (LAMBDA, theoremes[t1].gauche),
				      theoremes[t2].gauche),
				  theoremes[t3].gauche);
	theoremes[t].droite = subst (theoremes[t1].droite,
					theoremes[t2].droite,
						theoremes[t3].droite);
}

def_t3 (t_subst, d_subst)

d_1 (t, t1) theoreme t, t1;
{
	/* a = b et a atomique -> 1 a = I */
	vt (t1)
	theoremes[t].regle = r_1;
	theoremes[t].n_premisses = 1;
	theoremes[t].premisses[1] = t1;
	if (atom(theoremes[t1].gauche))
		theoremes[t].gauche = ap (_1, theoremes[t1].gauche);
	else
		theoremes[t].gauche = I;
	theoremes[t].droite = I;
}

def_t1 (t_1, d_1)

d_N (t, t1, t2) theoreme t, t1, t2;
{
	/* x = y, a = b, x n'apparait pas dans a -> N x a = I */
	vt(t1) vt(t2)
	theoremes[t].regle = r_N;
	theoremes[t].n_premisses = 2;
	theoremes[t].premisses[1] = t1;
	theoremes[t].premisses[2] = t2;
	if (occ (mg(t1), mg(t2)))
		theoremes[t].gauche = I;
	else
		theoremes[t].gauche = ap (ap (N, theoremes[t1].gauche),
						theoremes[t2].gauche);
	theoremes[t].droite = I;
}

def_t2 (t_N, d_N)


/*
d_transym (t, t1, t2) theoreme t, t1, t2;
{

}
*/

theoreme t_transym (t1, t2) theoreme t1, t2;
{
	return t_trans (t_sym(t1), t2);
}

theoreme chercher (expr x, expr y)
{
int i;
	if (flags & FLAG_TRACE)
	{
		indent ();
		printf ("chercher: x = %d = ", x);
		pfrexpr (x);
		printf (" y = %d = ", y);
		pfrexpr (y);
		printf ("\n");
	}
	for (i=0; i<ptr_th; i++) /*NTHEOREMES*/
	{
		if (theoremes[i].regle &&
			equal (theoremes[i].gauche, x) &&
			equal (theoremes[i].droite, y))
		{
				tr (i);
				return i;
		}
	}
	return -1;
}

theoreme new_th()
{
theoreme t;
	/*
	while (theoremes[ptr_th].regle && ptr_th > 0)
	{
		ptr_th--;
	}
	if (theoremes[ptr_th].regle)
		printf ("Erreur: debordement de la table des theoremes\n");
	return ptr_th;
	*/
	while (theoremes[ptr_th].regle)
	{
		if (ptr_th >= NTHEOREMES-1)
		{
			printf ("Erreur: debordement table des theoremes\n");
			print_theorems ();
			return -1;
		}
		ptr_th++;
	}
	return ptr_th;
}

theoreme constr (expr x)
{
theoreme t, tf, ta;
	t = chercher (x, x);
	tr (t);
	if (t > 0) return t;
	tr (t);
	if (atom(x)) return -1;
	tr (t);
	tf = constr (fnc(x));
	tr (tf);
	if (tf < 0) return -1;
	tr (tf);
	ta = constr (arg(x));
	tr (ta);
	if (ta < 0) return -1;
	tr (ta);
	/*
	t = new_th();
	d_ap (t, tf, ta);
	*/
	t = t_ap (tf, ta);
	tr (t);
	return t;
}

#define test(x) if ((x) == -1) return -1;
/* #define test(x) (((x) == -1) ? (return (-1)) : x) */
theoreme red0 (expr x, int flag_lambda)
{
theoreme r;
	niveau++;
	if (flags & FLAG_TRACE)
	{
		indent ();
		printf ("Reduction expr %d = ", x);
		pfrexpr (x);
		printf (" : ");
	}
	niveau++;
	r = red1 (x, flag_lambda);
	niveau--;
	if (flags & FLAG_TRACE)
	{
		indent ();
		printf ("Resultat reduction expr %d = ", x);
		pfrexpr (x);
		printf (" : \n");
		tr (r);
	}
	niveau--;
	return r;
}

theoreme red (expr x)
{
	return red0 (x, 0);
}

theoreme red_lambda (expr x)
{
	return red0 (x, 1);
}

indent ()
{
int i;
	for (i=0; i<=niveau; i++)
		printf (" | ");
}

theoreme red1 (expr x, int fl)
{
theoreme t, t1, t2, t3, t4, t5;
/*
    if (flags & FLAG_TRACE)
    {
	indent ();
	printf ("Reduction expr %d = ", x);
	pfrexpr (x);
	printf (" : ");
    }
*/
    if (flags & 2)
    {
	printf ("sizeof (I) = %d\n", sizeof(I));
	printf ("sizeof (fnc(x)) = %d\n", sizeof (fnc(x)));
	printf ("I < 0 = %d\n", I < 0);
	printf ("fnc(x) < 0 = %d\n", fnc(x) < 0);
	printf ("I = 0x%X, fnc(x) = 0x%X\n", I, fnc(x));
    }
    if (atom(x))
    {
	if (flags & FLAG_TRACE)
		printf ("atome.\n");
	/* return constr(x); */
	t = constr (x);
	test (t);
	return t;
    }
    if (fnc(x) == I)
    {
	if (flags & FLAG_TRACE)
		printf ("-Ix = x.\n");
	t1 = red0 (arg(x), fl);
	tr (t1);
	test (t1);
	tr (t1);
#ifdef AV_11_12_93
	t = new_th();
	tr (t);
	d_I (t, t1);
	tr (t);
#else
	t = t_I (t1);
	tr (t);
#endif
	return t;
    }
    if (atom(fnc(x)))
    {
	if (flags & FLAG_TRACE)
		printf ("-fx, f atome.\n");
	test (t1 = constr (fnc(x)));
	tr (t1);
	test (t2 = red0 (arg(x), fl));
	tr (t2);
#ifdef OLD
	t = new_th();
	d_ap (t, t1, t2);
#else
	t = t_ap (t1, t2);
#endif
	tr (t);
	return t;
    }
    if (fnc(fnc(x)) == K)
    {
	if (flags & FLAG_TRACE)
	{
		printf ("--Kxy = x.\n");
	}
	test (t1 = red0 (arg(fnc(x)), fl));
	tr (t1);
	test (t2 = red0 (arg(x), fl));
	tr (t2);
#ifdef AV_12_12_93
	t = new_th();
	d_K (t, t1, t2);
#else
	t = t_K (t1, t2);
#endif
	tr (t);
	return (t);
    }
    /*
    if (atom(fnc(fnc(x))))
    {
	t1 = constr (fnc(fnc(x)));
	test (t1);
	t2 = constr (arg(fnc(x)));
	test (t2);
	t3 = red0 (arg(x), fl);
#ifdef OLD
	t4 = new_th();
	d_ap (t4, t1, t2);
	t = new_th();
	d_ap (t, t4, t3);
#else
	t4 = t_ap (t1, t2);
	t = t_ap (t4, t3);
#endif
	return t;
    }
    */
    if (!atom (fnc(fnc(x))) && fnc(fnc(fnc(x))) == S)
    {
	if (flags & FLAG_TRACE)
		printf ("---Sxyz = --xz-yz.\n");
	t1 = red0 (arg(fnc(fnc(x))), fl); 	tr (t1); test (t1);
	tr (t1);
	t2 = red0 (arg(fnc(x)), fl);         tr (t2); test (t2);
	tr (t2);
	t3 = red0 (arg(x), fl);              tr (t3); test (t3);
	tr (t3);
#ifdef AV_12_12_93
	t4 = new_th();
	d_S (t4, t1, t2, t3);
#else
	t4 = t_S (t1, t2, t3);
	tr (t4);
#endif
	t5 = red0 (theoremes[t4].droite, fl);
	tr (t5);
	if (t5 == -1 || equal(theoremes[t5].gauche, theoremes[t5].droite))
	{
	    if (flags & FLAG_TRACE)
		printf ("\t--xz-yx irreductible\n");
	    return t4;
	}
	if (flags & FLAG_TRACE)
		printf ("\t--xz-yz reductible\n");
#ifdef OLD
	t = new_th();
	d_trans (t, t4, t5);
#else
	t = t_trans (t4, t5);
#endif
	tr (t);
	return t;
    }
    if (fl && !atom (fnc(fnc(x))) && fnc(fnc(fnc(x))) == LAMBDA)
    {
	if (flags & FLAG_TRACE)
		printf ("---^xyz = subst(x,y,z).\n");
	t1 = red0 (arg(fnc(fnc(x))), fl); 	tr (t1); test (t1);
	tr (t1);
	t2 = red0 (arg(fnc(x)), fl);         tr (t2); test (t2);
	tr (t2);
	t3 = red0 (arg(x), fl);              tr (t3); test (t3);
	tr (t3);
#ifdef AV_12_12_93
	t4 = new_th();
	d_S (t4, t1, t2, t3);
#else
	t4 = t_subst (t1, t2, t3);
	tr (t4);
#endif
	t5 = red0 (theoremes[t4].droite, fl);
	tr (t5);
	if (t5 == -1 || equal(theoremes[t5].gauche, theoremes[t5].droite))
	{
	    if (flags & FLAG_TRACE)
		printf ("\tsubst(x,y,z) irreductible\n");
	    return t4;
	}
	if (flags & FLAG_TRACE)
		printf ("\tsubst(x,y,z) reductible\n");
#ifdef OLD
	t = new_th();
	d_trans (t, t4, t5);
#else
	t = t_trans (t4, t5);
#endif
	tr (t);
	return t;
    }
    if (flags & FLAG_TRACE)
	printf ("cas general.\n");
    t1 = red0 (fnc(x), fl); 	tr (t1); test (t1);
    tr (t1);
    t2 = red0 (arg(x), fl);  tr (t1); test (t2);
    tr (t2);
#ifdef OLD
    t3 = new_th();
    d_ap (t3, t1, t2);
#else
    t3 = t_ap (t1, t2);
    tr (t3);
#endif
    if (equal (theoremes[t3].gauche, theoremes[t3].droite))
    {
	if (flags & FLAG_TRACE)
		printf ("\tpas de reduction\n");
	return t3;
    }
    if (flags & FLAG_TRACE)
	printf ("\treduction\n");
    t4 = red0 (theoremes[t3].droite, fl);
    if (t4 == -1 || equal (theoremes[t4].gauche, theoremes[t4].droite))
    {
	if (flags & FLAG_TRACE)
		printf ("\tMembre droit irreductible\n");
	return t3;
    }
    if (flags & FLAG_TRACE)
	printf ("\tMembre droit reductible\n");
#ifdef OLD
    t = new_th();
    d_trans (t, t3, t4);
#else
    t = t_trans (t3, t4);
    tr (t);
#endif
    return t;
}

theoreme t_transit (t1, t2)
theoreme t1, t2;
{
	if (equal (mg(t1), md(t1)))
		return t2;
	if (equal (mg(t2), md(t2)))
		return t1;
	return t_trans (t1, t2);
}


theoreme redu (expr x, theoreme ax1, theoreme ax2)
{
int forme_Sfg;
theoreme rf, ra;
expr f1, a1, x1;
theoreme r1, r2, t1, t2, t3, t4, t5, t6;
	if (atom(x))
		return tr(constr(x));
	/* printf ("Avant: &x = 0x%X, x = %d, *0xFE22 = %d\n",
		&x, x, *(int *)0xFE22); */
	rf = redu (fnc(x), ax1, ax2);
	tr (rf);
	/* printf ("Apres: &x = 0x%X, x = %d, *0xFE22 = %d\n",
		&x, x, *(int *)0xFE22); */
	ra = redu (arg(x), ax1, ax2);
	tr (ra);
	f1 = md (rf);
	a1 = md (ra);
	if (equal(fnc(x),f1) && equal(arg(x),a1))
	{
		r1 = redu1 (x, ax1, ax2);
		tr (r1);
		if (equal (md(r1), x))
			return r1;
		r2 = redu (md(r1), ax1, ax2);
		tr (r2);
		if (mg(r2) == md(r2))
			return r1;
		if (mg(r1) == md(r1))
			return r2;
		return tr (t_trans (r1, r2));
	}
	x1 = ap (f1, a1);
	r1 = redu1 (x1, ax1, ax2);
	tr (r1);
	if (equal(md(r1),x))
		r2 = r1;
	r2 = redu (md(r1), ax1, ax2);
	tr (r2);
	/* return tr (t_transit (tr(t_transit (tr(t_ap(rf,ra)), r1)), r2));*/
	t3 = t_ap (rf, ra);
	tr (t3);
	t4 = t_transit (t3, r1);
	tr (t4);
	t5 = t_transit (t4, r2);
	tr (t5);
	return t5;
/*	t1 = t_trans (t_ap (rf, ra), r1);
	if (mg(r2) == md(r2))
		return t1;
	return t_trans (t1, r2); */

}

theoreme redu1 (expr x, theoreme a1, theoreme a2)
{
theoreme t1, t2, t3, t4, t5, t6, t7, t8;
int forme_SKfg;
	forme_SKfg = !atom(fnc(x)) && fnc(fnc(x))==S && !atom(arg(fnc(x)))
		&& fnc(arg(fnc(x)))==K;
	if (forme_SKfg  && arg(x) == I)
	{
	/* S (Kf) I = I */
		t1 = constr (arg(arg(fnc(x)))); test(t1);
		tr (t1);
		t2 = t_ap (a1, t1);
		tr (t2);
		t3 = t_I (t1);
		tr (t3);
		t4 = t_trans (t2, t3);
		tr (t4);
		t5 = red (mg(t4));
		tr (t5);
		t6 = t_sym (t5);
		tr (t6);
		t7 = t_trans (t6, t4);
		tr (t7);
		return t7;
	}
	if (forme_SKfg && !atom(arg(x)) && fnc(arg(x))==K)
	{
	/* S(Kf)(Ka) = K(fa) */
		t1 = constr (arg(arg(fnc(x)))); test(t1);
		tr (t1);
		t2 = constr (arg(arg(x))); test(t2);
		tr (t2);
		t3 = t_ap (t_ap (a2, t1), t2);
		tr (t3);
		t4 = red (mg(t3));
		tr (t4);
		t5 = t_sym (t4);
		tr (t5);
		t6 = t_trans (t5, t3);
		tr (t6);
		t7 = red (md(t3));
		tr (t7);
		t8 = t_trans (t6, t7);
		tr (t8);
		return t8;
	}
	return tr (constr (x));

}

theoreme abst (expr v, expr x)
{
theoreme t, t1, t2, t3, t4, t5, t6, t7;
    if (v == x)
    {
	test (t1 = constr (x));
	t = new_th();
	d_I (t, t1);
	return t;
    }
    if (!occ (v, x))
    {
	test (t1 = constr (v));
	test (t2 = constr (x));
	t = new_th();
	d_K (t, t1, t2);
	return t;
    }
    if (!occ (v, fnc(x)))
    {
	t = constr (x);
	return t;
    }
    /* \v.fa = S (\v.f) (\v.a) */
    /* S (\v.f) (\v.a) v = fa */
    t1 = abst (v, fnc(x)); 	/* (\v.f)v = f */	test (t1);
    t2 = abst (v, arg(x)); 	/* (\v.a)v = a */       test (t2);
#ifdef OLD
    t3 = new_th();
    d_ap (t3, t1, t2);     	/* (\v.f)v ((\v.a)v) = fa */
#else
    t3 = t_ap (t1, t2);
#endif
#if 0
    t4 = constr (fnc(x));       /* f = f */
    t5 = constr (arg(x));       /* a = a */
#endif
    t4 = constr (fnc(theoremes[t1].gauche));            test (t4);
    t5 = constr (fnc(theoremes[t2].gauche));            test (t5);
    t6 = constr (v);            /* v = v */             test (t6);
    t7 = new_th();
    d_S (t7, t4, t5, t6);       /* S (\v.f) (\v.a) v = (\v.f) v ((\v.a) v) */
				/* S f a v = f v (a v) */
#ifdef OLD
    t = new_th ();
    d_trans (t, t7, t3);
#else
    t = t_trans (t7, t3);
#endif
    return t;
}


theoreme ext (x, t, ext_I, ext_K, ext_S)
expr x;
theoreme t, ext_I, ext_K, ext_S;
{
theoreme te, t1, t2, t3, t4, t5, t6, t7, t8, t9;

	if (theoremes[t].gauche == x && theoremes[t].droite == x)
		return constr (I);
	if (!occ (x, theoremes[t].gauche) &&
	    !occ (x, theoremes[t].droite))
	{
		/*
		te = new_th ();
		d_ap (te, constr(K), t);
		*/
		te = t_ap (constr(K), t);
		return te;
	}
	if (theoremes[t].regle == r_axiom)
		return -1;
	switch (theoremes[t].regle)
	{
		case r_sym:
			return t_sym (ext (x, theoremes[t].premisses[1],
						ext_I, ext_K, ext_S));
		case r_trans:
			/* te = new_th (); */
#ifdef OLD
			te = t_trans (ext (x, theoremes[t].premisses[1],
						ext_I, ext_K, ext_S),
				      ext (x, theoremes[t].premisses[2],
						ext_I, ext_K, ext_S));
#else
			tr (t);
			tr (theoremes[t].premisses[1]);
			tr (theoremes[t].premisses[2]);
			t1 = ext (x, theoremes[t].premisses[1],
						ext_I, ext_K, ext_S);
			tr (t1);
			t2 = ext (x, theoremes[t].premisses[2],
						ext_I, ext_K, ext_S);
			tr (t2);
			tr (t1);
			tr (theoremes[t].premisses[1]);
			tr (theoremes[t].premisses[2]);
			te = t_trans (t1, t2);
			tr (te);
#endif
			return te;
		case r_ap:
			t1 = ext (x, theoremes[t].premisses[1],
					ext_I, ext_K, ext_S);
			t2 = ext (x, theoremes[t].premisses[2],
					ext_I, ext_K, ext_S);
			t3 = t_ap (constr(S), t1);
			t4 = t_ap (t3, t2);
			return t4;
		case r_I:
			t1 = ext (x, theoremes[t].premisses[1],
					ext_I, ext_K, ext_S);
			return t_trans (t_ap (ext_I, t1),
					t_I (constr (theoremes[t1].droite)));
		case r_K:
			t1 = ext (x, theoremes[t].premisses[1],
					ext_I, ext_K, ext_S);
			if (flags & 8) print_theorem(t1);
			t2 = ext (x, theoremes[t].premisses[2],
					ext_I, ext_K, ext_S);
			if (flags & 8) print_theorem(t2);
			t3 = t_ap (t_ap (ext_K, t1), t2);
			if (flags & 8) print_theorem(t3);
			t4 = t_K (constr (theoremes[t1].droite),
				  constr (theoremes[t2].droite));
			if (flags & 8) print_theorem(t4);
			t5 = t_trans (t3, t4);
			if (flags & 8) print_theorem(t5);
			t6 = red (theoremes[t5].gauche);
			if (flags & 8) print_theorem(t6);
			t7 = t_sym (t6);
			if (flags & 8) print_theorem(t7);
			return t_trans (t7, t5);
		case r_S:
			t1 = ext (x, theoremes[t].premisses[1],
					ext_I, ext_K, ext_S);
			if (flags & 8)
			{
			    fprintf (sortie, "ext(S) ext 1 \t t1: ");
			    print_theorem (t1);
			}
			t2 = ext (x, theoremes[t].premisses[2],
					ext_I, ext_K, ext_S);
			if (flags & 8)
			{
			    fprintf (sortie, "ext(S) ext 2 \t t2: ");
			    print_theorem (t2);
			}
			t3 = ext (x, theoremes[t].premisses[3],
					ext_I, ext_K, ext_S);
			if (flags & 8)
			{
			    fprintf (sortie, "ext(S) ext 3 \t t3: ");
			    print_theorem (t3);
			}
			t4 = t_ap (t_ap (t_ap (ext_S, t1), t2), t3);
			if (flags & 8)
			{
			    fprintf (sortie, "ext(S) ap    \t t4: ");
			    print_theorem (t4);
			}
			t5 = red (theoremes[t4].gauche);
			if (flags & 8)
			{
			    fprintf (sortie, "ext(S) red g.\t t5: ");
			    print_theorem (t5);
			}
			t6 = t_sym (t5);
			if (flags & 8)
			{
			    fprintf (sortie, "ext(S) sym   \t t6: ");
			    print_theorem (t6);
			}
			t7 = t_trans (t6, t4);
			if (flags & 8)
			{
			    fprintf (sortie, "ext(S) trans \t t7: ");
			    print_theorem (t7);
			}
			t8 = red (theoremes[t7].droite);
			if (flags & 8)
			{
			    fprintf (sortie, "ext(S) red d.\t t8: ");
			    print_theorem (t8);
			}
			return t_trans (t7, t8);
		default:
			printf ("Erreur ext: regle incorrecte\n");
	}
}



theoreme print_theorem (theoreme t)
{
int i;
	/* tr (t); */
	if (theoremes[t].regle >= 0x20 && theoremes[t].regle <= 0x7F)
	fprintf (sortie, "d %d: %c ",
		t, theoremes[t].regle);
	else
		fprintf (sortie, "d %d: 0x%02X ", t, theoremes[t].regle);
	if (theoremes[t].regle == r_axiom)
	{
		fprintf (sortie, "= ");
		pfrexpr (theoremes[t].gauche);
		fprintf (sortie, " ");
		pfrexpr (theoremes[t].droite);
		fprintf (sortie, " ");
	}
	for (i=1; i<=theoremes[t].n_premisses; i++)
		fprintf (sortie, "%d ", theoremes[t].premisses[i]);
	fprintf (sortie, "-> ");
	if (theoremes[t].regle != r_axiom)
	{
		pfrexpr (theoremes[t].gauche);
		fprintf (sortie, " = ");
		pfrexpr (theoremes[t].droite);
		fprintf (sortie, " ; ");
	}
	printexpr (theoremes[t].gauche);
	fprintf (sortie, " = ");
	printexpr (theoremes[t].droite);
	fprintf (sortie, ".\n");
	return t;
}

print_theorems ()
{
int i;
	for (i=0; i<NTHEOREMES /* i <= ptr_th */; i++)
		if (theoremes[i].regle)
			print_theorem (i);
}

int arite (char regle)
{
	switch (regle)
	{
		case r_axiom: return 0;
		case r_sym: case r_I: case r_1: return 1;
		case r_trans: case r_ap: case r_K: case r_N: return 2;
		case r_S: case r_subst: return 3;
		default:
			/* printf ("Arite non definie pour regle %c\n",
				regle); */
			return -1;
	}
}

dem (t, regle, premisses)
theoreme t;
char regle;
theoreme premisses[];
{
	switch (regle)
	{
		case r_sym: 	d_sym 	(t, premisses[1]); break;
		case r_trans:   d_trans (t, premisses[1], premisses[2]); break;
		case r_ap:	d_ap 	(t, premisses[1], premisses[2]); break;
		case r_I:	d_I 	(t, premisses[1]); break;
		case r_K:	d_K	(t, premisses[1], premisses[2]); break;
		case r_S:	d_S	(t, premisses[1], premisses[2],
					    premisses[3]);               break;
		case r_subst:   d_subst (t, premisses[1], premisses[2],
					    premisses[3]); break;
		case r_1:	d_1	(t, premisses[1]); break;
		case r_N:	d_N 	(t, premisses[1], premisses[2]); break;
		default:
			printf ("Regle inconnue %c\n", regle);
	}
}

saisir_theoreme ()
{
char regle;
theoreme t, premisses[NPREMISSES];
int i, n;
expr a, b;
char c;

saisie:
	fscanf (entree, "%d", &t);
	if (feof(entree))
	{
		entree=stdin;
		goto saisie;
	}
	do regle=getc(entree);
	/* while ((n = arite(regle)) == -1 && regle != 'q'); */
	while (regle==' ' || regle=='\t' || regle==':');
	if ((n=arite(regle)) == -1)
	{
		printf ("Erreur: regle %c non definie\n", regle);
		return -1;
	}
	/*if (regle == 'q')
		return 0;*/
	for (i=1; i<=n; i++)
		fscanf (entree, "%d", &(premisses[i]));
	if (regle == r_axiom)
	{
		/* printf ("Axiome ? "); */
		/*
		a = readexpr ();
		b = readexpr ();
		*/
		readeq (&a, &b);
		d_axiom (t, a, b);
	}
	else
	dem (t, regle, premisses);
	if (flags & FLAG_VERBOSE)
	    print_theorem (t);
	do c=getc(entree);
	while (c!=10);
	return 1;
}

c_ligne ()
{
	if (flags & FLAG_COMPTEUR)
		printf ("\n");
}

memcpy1 (char *dest, char *src, int n)
{
	memcpy (dest, src, n);
}

theoreme simplif (theoreme t)
{
theoreme t1, t2, t3, t4, t5;
				tp (t);
				tr (t);
				t1 = red (mg(t));
				tr (t1);
				t2 = red (md(t));
				tr (t2);
				t3 = t_sym (t1);
				tr (t3);
				t4 = t_trans1 (t3, t);
				tr (t4);
				t5 = t_trans1 (t4, t2);
				tr (t5);
}

test1 ()
{
expr x, y, v;
char c, cn;
char filename[200];
FILE *f, *sortie1;
char nom[TAILLE_NOM+1];
int i, nr;
char source[200];
theoreme t, t1, t2, t3, t4, t5, t6, t7, ext_I, ext_K, ext_S, te, ax1, ax2;
theoreme t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18;
theoreme /*tr*/ res;
int status;

/*
	printexpr (ap(ap(S,ap(K,S)),I));
	printf("\n");
	x = readexpr();
	printexpr (x);
	printf ("\n");
*/
	/* while (saisir_theoreme()); */
	for (;;)
	{
	saisie:
		c = getc(entree);
		if (feof(entree))
		{
			entree = stdin;
			goto saisie;
		}
		switch (c)
		{
			case 'd': saisir_theoreme(); break;
			case 'q': return;
			case 'F': fscanf (entree, "%X", &flags); break;
			case 's': fscanf (entree, "%s", filename);
				  if (!strcmp(filename, "-"))
					f = stdout;
				  else
					f = fopen (filename, "w");
				  if (f == NULL)
				  {
					printf ("Erreur fopen %s\n", filename);
					perror ("fopen");
				  }
				  else
				  {
					sortie1 = sortie;
					sortie = f;
					print_theorems ();
					sortie = sortie1;
					if (f != stdout)
					{
						putc ('\n', f);
						fflush (f);
						status = fclose (f);
						if (status)
							printf ("Erreur fclose %s\n",
								 filename);
					}
				  }
				  break;
			case 'l':
				fscanf (entree, "%s", filename);
				f = fopen (filename, "r");
				if (f == NULL)
				{
					printf ("Erreur fopen %s\n", filename);
					perror ("fopen");
				}
				else
				{
					entree = f;
				}
				break;
			case 't':
				fscanf (entree, "%d", &t);
				/* tr (t); */
				print_theorem (t);
				/* tr = t; */
				res = t;
				break;
			case ' ': case 10: case 13: case '\t': case 0:
				break;
			case '<':

			i = 0;
			cn = getc(entree);
			while (cn != fin_nom /*&& i<TAILLE_NOM*/)
			{
				if (i < TAILLE_NOM)
					nom[i++] = cn;
				cn = getc(entree);
			}
			if (i < TAILLE_NOM)
				nom[i] = 0;
			else
				nom[TAILLE_NOM] = 0;
			nr = num_routine (nom);

			gets(source);
			coder (routines[nr].instr, source);
			break;

			case '&':
				gets(source);
				coder (routines[0].instr, source);
				interp (0);
				break;

			case 'r':
				x = readexpr();
				/*
				i_emp (red (x));
				print_theorem (pile[bas]);
				*/
				t = red (x);
				c_ligne ();
				print_theorem (t);
				res = t;
				break;

			case '=':
				fscanf (entree, "%d", &t);
				t5 = simplif (t);

				/*
				tp (t);
				tr (t);
				t1 = red (mg(t));
				tr (t1);
				t2 = red (md(t));
				tr (t2);
				t3 = t_sym (t1);
				tr (t3);
				t4 = t_trans (t3, t);
				tr (t4);
				t5 = t_trans (t4, t2);
				tr (t5);
				*/

				print_theorem (t5);
				res = t5;
				break;
			case '^':
				fscanf (entree, "%d", &t);
				tp (t);
				tr (t);
				t1 = red_lambda (mg(t));
				tr (t1);
				t2 = red_lambda (md(t));
				tr (t2);
				t3 = t_sym (t1);
				tr (t3);
				t4 = t_trans (t3, t);
				tr (t4);
				t5 = t_trans (t4, t2);
				tr (t5);
				print_theorem (t5);
				res = t5;
				break;

			case 'c':
				x = readexpr ();
				t = constr (x);
				print_theorem (t);
				res = t;
				break;

			case 'a':
				v = readexpr();
				x = readexpr();
				/*
				i_emp (abst (v, x));
				print_theorem (pile[bas]);
				*/
				t = abst (v, x);
				c_ligne ();
				print_theorem (t);
				res = t;
				break;

			case 'e':
				x = readexpr();
				fscanf (entree, "%d", &t); tp(t);
				fscanf (entree, "%d", &ext_I); tp(ext_I);
				fscanf (entree, "%d", &ext_K); tp (ext_K);
				fscanf (entree, "%d", &ext_S); tp (ext_S);
				te = ext (x, t, ext_I, ext_K, ext_S);
				c_ligne ();
				print_theorem (te);
				res = te;
				break;
			case 'R':
				x = readexpr ();
				fscanf (entree, "%d", &ax1); tp(ax1);
				fscanf (entree, "%d", &ax2); tp(ax2);
				ax_1 = ax1;
				ax_2 = ax2;
				t = redu (x, ax1, ax2);
				c_ligne ();
				print_theorem (t);
				res = t;
				break;
			case 'E':
				v = readexpr ();
				fscanf (entree, "%d", &t);     	tp(t);
				fscanf (entree, "%d", &ext_I); 	tp(ext_I);
				fscanf (entree, "%d", &ext_K);	tp(ext_K);
				fscanf (entree, "%d", &ext_S);	tp(ext_S);
				fscanf (entree, "%d", &ax1);	tp(ax1);
				fscanf (entree, "%d", &ax2);	tp(ax2);
				ax_1 = ax1;
				ax_2 = ax2;
				t1 = ext (v, t, ext_I, ext_K, ext_S);
				tr (t1);
				x = mg (t1);
				y = md (t1);
				t2 = redu (x, ax1, ax2);
				tr (t2);
				t3 = redu (y, ax1, ax2);
				tr (t3);
				t4 = t_sym (t2);
				tr (t4);
				t5 = t_trans (t4, t1);
				tr (t5);
				t6 = t_trans (t5, t3);
				tr (t6);
				c_ligne ();
				print_theorem (t6);
				res = t6;
				break;
			case '!':
				fscanf (entree, "%d", &t1); /* !abc = !abd */
				fscanf (entree, "%d", &t2); /* a = b */
				fscanf (entree, "%d", &ax1); /* S!I = KI */

				t3 = t_ap (ax1, t2); tr(t3);	/* S!Ia = KIb */
				t4 = simplif (t3); tr(t4);	/* !aa = I */
				t5 = constr (ap (E_aff, mg(t2))); /* !a = !a */
				tr (t5);
				t6 = t_ap (t5, t2); tr (t6);	/* !aa = !ab */
				t7 = t_sym (t6); tr (t7);	/* !ab = !aa */
				t8 = t_trans1 (t7, t4); tr(t8); /* !ab = I */
				t9 = constr (arg(mg(t1)));	/* c = c */
				tr(t9);
				t10 = t_ap (t8, t9); tr(t10);	/* !abc = Ic */
				t11 = simplif (t10); tr(t11);	/* !abc = c */
				t12 = t_sym (t11); tr(t12);	/* c = !abc */
				t13 = t_trans1 (t12, t1); tr(t13);/* c = !abd */
				t14 = constr (arg(md(t1)));	/* d = d */
				tr(t14);
				t15 = t_ap (t8, t14); tr (t15); /* !abd = Id */
				t16 = simplif (t15); tr (t16);  /* !abd = d */
				t17 = t_trans1 (t13, t16);	/* c = d */
				tr (t17);
				res = t17;
				c_ligne ();
				print_theorem (res);
				break;

			case '\'': /* ! */
				i_emp (res);
				break;

			case '>':
				fscanf (entree, "%d", &t);
				tp (t);
				/* tr (t); */
				tr (res);
				/* memcpy (&(theoremes[t]), &(theoremes[res]),
					sizeof(theoremes[t])); */
				/* memcpy1 (p_theoremes+t, p_theoremes+res,
					sizeof(theoremes[t])); */
				theoremes[t] = theoremes[res];
				tr (t);
				res = t;
				tr (res);
				break;

			default:
				break_debug ();
				printf ("Commande %c incorrecte\n", c);
		}
	}
}

map ()
{
FILE *mf;

	mf = fopen ("lc.map", "w");
	if (mf == NULL)
	{
		printf ("Impossible d'ouvrir le fichier map\n");
		perror ("fopen");
		return;
	}
#define mfn(f) fprintf (mf, "%4X " #f "\n", f);
	mfn (readeq);
	mfn (abstract);
	mfn (occ);
	mfn (interp);
	mfn (print_theorem);
	mfn (print_theorems);
	mfn (alloc_theoremes);
	mfn (break_debug);

	fclose (mf);
}

main ()
{
/*
	printf ("size = %d\n", sizeof(p_theoremes));
*/
#ifdef ALLOC
	p_theoremes = MK_FP (0x1234, 0x5678);
#endif
	printf ("Demonstration de theoremes de logique combinatoire\n");
	map();
	init ();
	test1 ();
}

