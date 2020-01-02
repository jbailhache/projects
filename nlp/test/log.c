
/*
	Representation des propositions :
	connecteurs : et p q, non p
	(logique modale: [a] p)
		A sait que...
		  pense que...
	propositions de base: pred o1 ... on
		oi = objet i ou valeur v (v: entier, reel (avec unite),
						chaine)

	exemple:
		le chat poursuit la souris :

			defini o(1) &
			chat o(1) &
			poursuit o(1) o(2) &
			defini o(2) &
			souris o(2)

		le chat poursuit rapidement la souris :

			defini o(1) &
			chat o(1) &
			rapidement o(1) o(2) &
			poursuit o(2) o(3) &
			defini o(3) &
			souris o(3)

		Pierre a 3 chats (au moins)

			au_moins_n (3, \x.defini o(1) &
					  nom o(1) v("Pierre") &
					  a o(1) x &
					  chat x)

			defini o(1) &
			nom o(1) v("Pierre") &
			a o(1) o(2) &
			a o(1) o(3) &
			a o(1) o(4) &
			chat o(2) &
			chat o(3) &
			chat o(4) &
			non (egal o(2) o(3)) &
			non (egal o(2) o(4)) &
			non (egal o(3) o(4)) &

		Pierre a 3 chats (exactement)

			idem +
			non (a o(1) o(5) &
				chat o(5) &
				non (egal o(2) o(5)) &
				non (egal o(3) o(5)) &
				non (egal o(4) o(5)))

		Pierre a 8 ans

			[il y a 8 ans] (defini o(1) &
					nom o(1) v("Pierre") &
					naitre o(1))

			ou

			defini o(1) &
			nom o(1) v("Pierre") &
			il_y_a v(8 ans) o(1) o(2)
			nait o(2)






*/

#include <stdlib.h>
#include <stdio.h>
#include <errno.h>

#include "stream.h"
#include "coroutines.h"

/*#include "trace.h"*/

#define ALLOC(p) \
	{ \
		(p) = malloc (sizeof (*(p))); \
		if ((p) == NULL) \
		{                 \
			fprintf (stderr, "Cannot allocate memory in %s line %d\n", \
				__FILE__, __LINE__); \
			exit (-1); \
		} \
	}

error (char *s)
{
	fprintf (stderr, s);
	exit (-1);
}

typedef struct fonction
{
	int (*f) ();
	void *p;
} *fonction;

#define CALL(fp) (*((fp)->f)) ((fp)->p

// enum languages { FRANCAIS, ENGLISH, ITALIANO, ESPANOL, DEUTSCH, ESPERANTO };

#define FRANCAIS 1
#define ENGLISH 2
#define ITALIANO 3
#define ESPANOL 4
#define DEUTSCH 5
#define ESPERANTO 6

#define LANGUAGE ESPERANTO

enum type_obj
{
	OBJ_VAR,
	OBJ_VINT,
	OBJ_VREAL,
	OBJ_VSTR
};

typedef struct object *obj;

struct object
{
	enum type_obj type;
	union
	{
		int var;
		int vint;
		struct
		{
			double val;
			char *unit;
		} vreal;
		char *vstr;
	} val;
};

obj new_var ()
{
static int last_var;
obj o;
	last_var++;
	ALLOC (o)
	o->type = OBJ_VAR;
	o->val.var = last_var;
	return o;
}

obj o_vint (int n)
{
obj o;
	ALLOC (o)
	o->type = OBJ_VINT;
	o->val.vint = n;
	return o;
}

obj o_vstr (char *s)
{
obj o;
	ALLOC (o)
	o->type = OBJ_VSTR;
	o->val.vstr = s;
	return o;
}


enum type_pred
{
	PRED_ART,
	PRED_VERB,
	PRED_PREP,
	PRED_NOM,
	PRED_CONJ_NOM,
	PRED_ADJ_PRE,
	PRED_ADJ_POST,
	PRED_PREP_ADJ,
	PRED_CONJ/*ADJ*/,
	PRED_ADV,
	PRED_SPECIAL
};

#define PRED_ADJ PRED_ADJ_PRE

typedef struct predicat *pred;

#define FLAG_PRONOM 1
#define FLAG_NOM_PROPRE 2
#define FLAG_ACCUSATIF 4
#define FLAG_PLURIEL 8
#define FLAG_PRESENT 0x10
#define FLAG_PASSE 0x20
#define FLAG_FUTUR 0x40
#define FLAG_CONDITIONNEL 0x80
#define FLAG_VOLITIF 0x100 /* imperatif */
#define FLAG_INFINITIF 0x200
#define FLAG_ACTIF 0x400
#define FLAG_COORD 0x800
#define FLAG_NEUTRE 0x1000
#define FLAG_MASCULIN 0x2000
#define FLAG_FEMININ 0x4000


struct predicat
{
	int arity;
	enum type_pred type;
	int flags;
	char *name;
};

pred predic (int arity, enum type_pred type, int flags, char *name)
{
pred p;
	ALLOC (p)
	p->arity = arity;
	p->type = type;
	p->flags = flags;
	p->name = name;
	return p;
}

print_pred (pred p)
{
	printf ("PRED %d %d %X <%s>\n",
		p->arity, p->type, p->flags, p->name);
}

#define MAX_ARG 4	/* nombre maximum d'arguments d'un predicat */

enum type_prop
{
	PROP_F,
	PROP_V,
	PROP_ELEM,
	PROP_NEG,
	PROP_CONJ
};

typedef struct proposition *prop;

struct proposition
{
	enum type_prop type;
	union
	{
		struct
		{
			pred p;
			obj a[MAX_ARG];
		} elem;
		prop neg;
		/*
		struct
		{
			prop p1;
			prop p2;
		} conj;
		*/
		prop p[2];
	} val;
};

prop ap0 (pred p)
{
prop r;
	if (p->arity != 0)
		error ("Bad arity");
	ALLOC (r)
	r->type = PROP_ELEM;
	r->val.elem.p = p;
	return r;
}

prop ap1 (pred p, obj a)
{
prop r;
	if (p->arity != 1)
		error ("Bad arity");
	ALLOC (r)
	r->type = PROP_ELEM;
	r->val.elem.p = p;
	r->val.elem.a[0] = a;
	return r;
}

prop ap2 (pred p, obj a, obj b)
{
prop r;
	if (p->arity != 2)
		error ("Bad arity");
	ALLOC (r)
	r->type = PROP_ELEM;
	r->val.elem.p = p;
	r->val.elem.a[0] = a;
	r->val.elem.a[1] = b;
	return r;
}

prop ap3 (pred p, obj a, obj b, obj c)
{
prop r;
	if (p->arity != 3)
		error ("Bad arity");
	ALLOC (r)
	r->type = PROP_ELEM;
	r->val.elem.p = p;
	r->val.elem.a[0] = a;
	r->val.elem.a[1] = b;
	r->val.elem.a[2] = c;
	return r;
}

prop not (prop p)
{
prop np;
	ALLOC (np);
	np->type = PROP_NEG;
	np->val.neg = p;
	return np;
}

prop and (prop p, prop q)
{
prop r;
	if (p == NULL)
		return q;
	if (q == NULL)
		return p;
	ALLOC (r)
	r->type = PROP_CONJ;
	/* r->val.conj.p1 = p; */
	r->val.p[0] = p;
	r->val.p[1] = q;
	return r;
}

struct predicat pred_defini[1] = {{ 1, PRED_ART, 0,
#if (LANGUAGE == FRANCAIS)
						"le"
#endif
#if (LANGUAGE == ENGLISH)
						"the"
#endif
#if (LANGUAGE == DEUTSCH)
						"das"
#endif
#if (LANGUAGE == ESPERANTO)
						"la"
#endif
							}};

struct predicat passe[1] = {{ 1, PRED_SPECIAL, 0, "pasint" }};
struct predicat futur[1] = {{ 1, PRED_SPECIAL, 0, "venont" }};

struct predicat fin_prop[1] = {{ 1, PRED_SPECIAL, 0, "." }};

struct proposition prop_vrai[1] = {{ PROP_V }};

struct predicat io[1] = {{ 1, PRED_NOM, 0, "i" }};
struct predicat ion[1] = {{ 1, PRED_NOM, FLAG_ACCUSATIF, "i" }};

prop example1 ()
{
obj chien, chat, souris, poursuite, jardin;
prop p;
	chien = new_var();
	chat = new_var();
	souris = new_var();
	poursuite = new_var();
	jardin = new_var();
#if (LANGUAGE == FRANCAIS)
	p = not(and (ap1 (pred_defini, chien),
		and (ap1 (predic (1, PRED_NOM, 0, "chien"), chien),
		and (ap3 (predic (3, PRED_VERB, 0, "poursuivre"), poursuite,
			chien, chat),
		and (ap1 (pred_defini, chat),
		and (ap1 (predic (1, PRED_NOM, 0, "chat"), chat),
		/*
		and (ap2 (predic (2, PRED_VERB, 0, "poursuivre"), chat, souris),
		*/
		and (ap3 (predic (3, PRED_VERB, 0, "poursuivre"), poursuite,
			chat, souris),
		and (ap1 (predic (1, PRED_ADV, 0, "vite"), poursuite),
		and (ap1 (pred_defini, souris),
		and (ap1 (predic (1, PRED_ADJ_PRE, 0, "petit"), souris),
		and (ap1 (predic (1, PRED_ADJ_POST, 0, "gris"), souris),
		and (ap1 (predic (1, PRED_ADJ_POST, 0, "apetissant"), souris),
		and (ap1 (predic (1, PRED_NOM, 0, "souris"), souris),
			prop_vrai)))))))))))));
#endif
#if (LANGUAGE == ESPERANTO)
	p = not(
		/*
		and (ap1 (pred_defini, chien),
		and (ap1 (predic (1, PRED_NOM, 0, "hund"), chien),
		*/
		and (ap1 (predic (1, PRED_NOM, FLAG_PRONOM, "ghi"), chien),
		and (ap3 (predic (3, PRED_VERB, 0, "postkur"), poursuite,
			chien, chat),
		and (ap1 (pred_defini, chat),
		and (ap1 (predic (1, PRED_NOM, 0, "kat"), chat),
		/*
		and (ap2 (predic (2, PRED_VERB, 0, "postkur"), chat, souris),
		*/
		and (ap3 (predic (3, PRED_VERB, 0, "postkur"), poursuite,
			chat, souris),
		and (ap1 (predic (1, PRED_ADV, 0, "rapid"), poursuite),
		and (ap2 (predic (2, PRED_PREP, 0, "en"), poursuite, jardin),
		and (ap1 (predic (1, PRED_NOM, 0, "gharden"), jardin),
		and (ap1 (passe, poursuite),
		and (ap1 (pred_defini, souris),
		and (ap1 (predic (1, PRED_ADJ_PRE, 0, "et"), souris),
		and (ap1 (predic (1, PRED_ADJ_PRE, 0, "griz"), souris),
		and (ap1 (predic (1, PRED_ADJ_POST, 0, "apetitigant"), souris),
		and (ap1 (predic (1, PRED_NOM, 0, "mus"), souris),
			prop_vrai)))))))))))))))/*)*/;
#endif

	return p;
}

prop verbe_de_prop (prop p)
{
prop verbe;
	/* si c'est un verbe on le rend */
	if (p->type == PROP_ELEM && p->val.elem.p->type == PRED_VERB)
		return p;
	if (p->type != PROP_CONJ)
		return NULL;
	verbe = verbe_de_prop (p->val.p[0]);
	if (verbe != NULL)
		return verbe;
	return verbe_de_prop (p->val.p[1]);
}

#if 0
prop nom_de_obj (prop p, obj a)
{
prop nom;
	/* si c'est ce nom on le rend */
	if (p->type == PROP_ELEM && p->val.elem.p->type == PRED_NOM &&
		p->val.elem.a[0] == a)
		return p;
	if (p->type != PROP_CONJ)
		return NULL;
	nom = nom_de_obj (p->val.conj.p1, a);
	if (nom != NULL)
		return nom;
	return nom_de_obj (p->val.conj.p2, a);
}
#endif

prop mot_obj (enum type_prop t, prop p, obj a)
{
prop mot;
	/* si c'est ce mot on le rend */
	if (p->type == PROP_ELEM && p->val.elem.p->type == t &&
		(p->val.elem.a[0] == a || a == -1))
		return p;
	if (p->type != PROP_CONJ)
		return NULL;
	mot = mot_obj (t, p->val.p[0], a);
	if (mot != NULL)
		return mot;
	return mot_obj (t, p->val.p[1], a);
}

/* mots_obj (enum type_prop t, prop p, obj a, fonction f)
{
	if (p->type == PROP_ELEM && p->val.elem.p->type == t &&
		p->val.elem.a[0] == a)
		return p;

}
*/

mots_obj (struct { enum type_prop t; prop p; obj a; } *param,
		struct coroutine *me)
{
struct coroutine calling;
	calling.calling = me->env;
	calling.env = me->calling;
	mots_obj1 (&calling, param->t, param->p, param->a);
	call_coroutine (&calling, -1);
}

mots_obj1 (struct coroutine *calling, enum type_prop t, prop p, obj a)
{
	if (p->type == PROP_ELEM && p->val.elem.p->type == t &&
		(p->val.elem.a[0] == a || a == -1))
		call_coroutine (calling, p);
	else if (p->type != PROP_CONJ)
		/* call_coroutine (calling, NULL) */;
	else
	{
	int i;
		for (i=0; i<2; i++)
			mots_obj1 (calling, t, p->val.p[i], a);
	}

}

prop_verif (struct { prop p; fonction f; } *param,
		struct coroutine *me)
{
struct coroutine calling;
	calling.calling = me->env;
	calling.env = me->calling;
	prop_verif1 (&calling, param->p, param->f);
	call_coroutine (&calling, -1);
}

prop_verif1 (struct coroutine *calling, prop p, fonction f)
{
	/*if (p->type == PROP_ELEM && p->val.elem.p->type == t &&
		(p->val.elem.a[0] == a || a == -1))*/
	if (CALL (f), p))
		call_coroutine (calling, p);
	else if (p->type != PROP_CONJ)
		/* call_coroutine (calling, NULL) */;
	else
	{
	int i;
		for (i=0; i<2; i++)
			prop_verif1 (calling, p->val.p[i], f);
	}

}

#if 0
init_mots_obj (struct coroutine *cr, enum type_prop t, prop p, obj a)
{
jmp_buf calling, env;
int stack [4000];
struct { enum type_prop t; prop p; obj a; } param;

}
#endif

synthese_gnom (struct put_fnct *put, prop p, obj a, int akuzativo)
{
prop nom;
prop article;
prop adjectif;
prop prep_adj;
struct coroutine cr;
jmp_buf calling, env;
int stack1 [4000];
int stack2 [4000];
int stack3 [4000];
struct { enum type_prop t; prop p; obj a; } param;

/* on cherche l'article */
	/* article = article_obj (p, a); */
	article = mot_obj (PRED_ART, p, a);
	if (article != NULL)
	{
		sput (put, article->val.elem.p->name);
		sput (put, " ");
	}

	cr.calling = &calling;
	cr.env = &env;
	param.t = PRED_ADJ_PRE;
	param.p = p;
	param.a = a;
	adjectif = start_coroutine (&cr, mots_obj, &param,
		stack1+(sizeof(stack1)-60)/sizeof(int));
	while (adjectif != -1)
	{
		sput (put, adjectif->val.elem.p->name);
#if (LANGUAGE == ESPERANTO)
		if (!(adjectif->val.elem.p->flags & FLAG_PRONOM))
			sput (put, "a");
		if (adjectif->val.elem.p->flags & FLAG_PLURIEL)
			sput (put, "j");
		if (akuzativo)
			sput (put, "n");
#endif
		sput (put, " ");
		adjectif = call_coroutine (&cr, 0);
	}

/* on cherche le nom */
	/* nom = nom_de_obj (p, a); */
	nom = mot_obj (PRED_NOM, p, a);
	if (nom != NULL)
	{
	sput (put, nom->val.elem.p->name);
#if (LANGUAGE == ESPERANTO)
	if (!(nom->val.elem.p->flags & FLAG_PRONOM))
		sput (put, "o");
	if (nom->val.elem.p->flags & FLAG_PLURIEL)
		sput (put, "j");
	if (akuzativo)
		sput (put, "n");
#endif
	}
/* on cherche les adjectifs */
/*
	adjectif = mot_obj (PRED_ADJ, p, a);
	if (adjectif != NULL)
	{
		sput (put, " ");
		sput (put, adjectif->val.elem.p->name);
	}
*/

	cr.calling = &calling;
	cr.env = &env;
	param.t = PRED_ADJ_POST;
	param.p = p;
	param.a = a;
	adjectif = start_coroutine (&cr, mots_obj, &param,
		stack2+(sizeof(stack2)-60)/sizeof(int));
	while (adjectif != -1)
	{
		sput (put, " ");
		sput (put, adjectif->val.elem.p->name);
#if (LANGUAGE == ESPERANTO)
		if (!(adjectif->val.elem.p->flags & FLAG_PRONOM))
			sput (put, "a");
		if (adjectif->val.elem.p->flags & FLAG_PLURIEL)
			sput (put, "j");
		if (akuzativo)
			sput (put, "n");
#endif
		adjectif = call_coroutine (&cr, 0);
	}
	/* on cherche les prepositions adjectives (de) */
	cr.calling = &calling;
	cr.env = &env;
	param.t = PRED_PREP_ADJ;
	param.p = p;
	param.a = a;
	prep_adj = start_coroutine (&cr, mots_obj, &param,
		stack3+(sizeof(stack3)-60)/sizeof(int));
	while (prep_adj != -1)
	{
		sput (put, " ");
		sput (put, prep_adj->val.elem.p->name);
		sput (put, " ");
		synthese_gnom (put, p, prep_adj->val.elem.a[1], 0);
		prep_adj = call_coroutine (&cr, 0);
	}

}

synthese_gverb (struct put_fnct *put, prop p, prop verbe, int aff)
{
/* synthese de phrases :
	chercher les verbes
	1 proposition par verbe
	sujet verbe complement
*/
prop adverbe, special, preposition;
struct coroutine cr;
jmp_buf calling, env;
int stack1 [4000];
int stack2[4000];
int stack3 [4000];
int stack4 [4000];
struct { enum type_prop t; prop p; obj a; } param;
enum { PRESENT, PASSE, FUTUR, CONDITIONNEL, VOLITIF } temps;

	/* verbe = verbe_de_prop (p); */
	/* sujet */
	synthese_gnom (put, p, verbe->val.elem.a[1], 0);
	if (!aff)
		sput (put, " ne");
#if (LANGUAGE == ESPERANTO)
/* on affiche les adverbes */
	cr.calling = &calling;
	cr.env = &env;
	param.t = PRED_ADV;
	param.p = p;
	param.a = verbe->val.elem.a[0];
	adverbe = start_coroutine (&cr, mots_obj, &param,
		stack1+(sizeof(stack1)-60)/sizeof(int));
	while (adverbe != -1)
	{
		sput (put, " ");
		sput (put, adverbe->val.elem.p->name);
#if (LANGUAGE == ESPERANTO)
		if (!(adverbe->val.elem.p->flags & FLAG_PRONOM))
			sput (put, "e");
#endif
		adverbe = call_coroutine (&cr, 0);
	}
#endif

	sput (put, " ");
	sput (put, verbe->val.elem.p->name);
	/* on cherche le temps */
	temps = PRESENT;
	cr.calling = &calling;
	cr.env = &env;
	param.t = PRED_SPECIAL;
	param.p = p;
	param.a = verbe->val.elem.a[0];
	special = start_coroutine (&cr, mots_obj, &param,
		stack2+(sizeof(stack2)-60)/sizeof(int));
	// printf ("\nspecial=0x%x\n", special);
	if (special == -1)
		;
	else if (special->val.elem.p == passe ||
		(verbe->val.elem.p->flags & FLAG_PASSE))
		temps = PASSE;
	else if (special->val.elem.p == futur ||
		(verbe->val.elem.p->flags & FLAG_FUTUR))
		temps = FUTUR;
	else if (verbe->val.elem.p->flags & FLAG_CONDITIONNEL)
		temps = CONDITIONNEL;
	else if (verbe->val.elem.p->flags & FLAG_VOLITIF)
		temps = VOLITIF;
#if (LANGUAGE == ESPERANTO)
	switch (temps)
	{
		case PRESENT: sput (put, "as"); break;
		case PASSE:   sput (put, "is"); break;
		case FUTUR:   sput (put, "os");
		case CONDITIONNEL: sput (put, "us"); break;
		case VOLITIF: sput (put, "u"); break;

	}
#endif
#if (LANGUAGE == FRANCAIS)
	if (!aff)
		sput (put, " pas");
#endif
#if (LANGUAGE == FRANCAIS)
/* on affiche les adverbes */
	cr.calling = &calling;
	cr.env = &env;
	param.t = PRED_ADV;
	param.p = p;
	param.a = verbe->val.elem.a[0];
	adverbe = start_coroutine (&cr, mots_obj, &param,
		stack3+(sizeof(stack3)-60)/sizeof(int));
	while (adverbe != -1)
	{
		sput (put, " ");
		sput (put, adverbe->val.elem.p->name);
#if (LANGUAGE == ESPERANTO)
		sput (put, "e");
#endif
		adverbe = call_coroutine (&cr, 0);
	}
#endif
	sput (put, " ");
	/* C.O.D. */
	synthese_gnom (put, p, verbe->val.elem.a[2], 1);

/* on affiche les prepositions */
	cr.calling = &calling;
	cr.env = &env;
	param.t = PRED_PREP;
	param.p = p;
	param.a = verbe->val.elem.a[0];
	preposition = start_coroutine (&cr, mots_obj, &param,
		stack4+(sizeof(stack4)-60)/sizeof(int));
	while (preposition != -1)
	{
		sput (put, " ");
		sput (put, preposition->val.elem.p->name);
		sput (put, " ");
		synthese_gnom (put, p, preposition->val.elem.a[1], 0);
		preposition = call_coroutine (&cr, 0);
	}

}

#if 0
synthese (struct put_fnct *put, prop p)
{
prop verbe;
struct coroutine cr;
jmp_buf calling, env;
int stack [5000];
struct { enum type_prop t; prop p; obj a; } param;

	cr.calling = &calling;
	cr.env = &env;
	param.t = PRED_VERB;
	param.p = p;
	param.a = -1;
	verbe = start_coroutine (&cr, mots_obj, &param, sizeof(stack)-60);
	while (verbe != -1)
	{
		synthese_gverb (put, p, verbe);
		verbe = call_coroutine (&cr, 0);
		if (verbe == -1)
			sput (put, ". ");
		else
			sput (put, "; ");
	}
}
#endif

int est_un_verbe (void *v, prop p)
{
	return (p->type == PROP_ELEM && p->val.elem.p->type == PRED_VERB);
}

int verbe_ou_neg (void *v, prop p)
{
int r;
	r = (p->type == PROP_ELEM && p->val.elem.p->type == PRED_VERB)
		|| (p->type == PROP_NEG);
	return r;
}

/* #define synthese(put,p) synthese_aff_neg(put,p,1) */

synthese (put, p)
{
	if (p == NULL)
		sput (put, "Mi ne komprenas.");
	else
		synthese_aff_neg (put, p, 1);
}

synthese_aff_neg (struct put_fnct *put, prop p, int aff)
{
prop verbe;
struct coroutine cr;
jmp_buf calling, env;
int stack [5000];
int *adr;
struct { prop p; fonction f; } param;
struct fonction f;

	cr.calling = &calling;
	cr.env = &env;
	param.p = p;
	param.f = &f;
	f.f = verbe_ou_neg /*est_un_verbe*/;
	adr = stack+(sizeof(stack)-60)/sizeof(int);
	// printf ("stack=0x%x adr=0x%x size=%d=0x%x\n", stack, adr, sizeof(stack), sizeof(stack));
	verbe = start_coroutine (&cr, prop_verif, &param, adr);
	while (verbe != -1)
	{
	    if (verbe->type == PROP_ELEM && verbe->val.elem.p->type == PRED_VERB)
	    {
		synthese_gverb (put, p, verbe, aff);
		verbe = call_coroutine (&cr, 0);
		if (verbe == -1)
			sput (put, ". ");
		else
		{
		   if (aff)
			sput (put, "; ");
		   else
			sput (put,
#if (LANGUAGE == FRANCAIS)
				" ou "
#endif
#if (LANGUAGE == ESPERANTO)
				" aw "
#endif
					);
		}
	    }
	    else if (verbe->type == PROP_NEG)
	    {
		synthese_aff_neg (put, verbe->val.neg, !aff);
		verbe = call_coroutine (&cr, 0);
	    }
	}
}
#if 0
synthese_aff_neg1 (struct put_fnct *put, prop p, int aff, int *stack)
{
prop verbe;
struct coroutine cr;
jmp_buf calling, env;
/* int stack [6000]; */
struct { prop p; fonction f; } param;
struct fonction f;

	cr.calling = &calling;
	cr.env = &env;
	param.p = p;
	param.f = &f;
	f.f = verbe_ou_neg /*est_un_verbe*/;
	verbe = start_coroutine (&cr, prop_verif, &param, sizeof(stack)-60);
	while (verbe != -1)
	{
	    if (verbe->type == PROP_ELEM && verbe->val.elem.p->type == PRED_VERB)
	    {
		synthese_gverb (put, p, verbe, aff);
		verbe = call_coroutine (&cr, 0);
		if (verbe == -1)
			sput (put, ". ");
		else
		{
		   if (aff)
			sput (put, "; ");
		   else
			sput (put,
#if (LANGUAGE == FRANCAIS)
				" ou "
#endif
#if (LANGUAGE == ESPERANTO)
				" aw "
#endif
					);
		}
	    }
	    else if (verbe->type == PROP_NEG)
	    {
		synthese_aff_neg1 (put, verbe->val.neg, !aff);
	    }
	    verbe = call_coroutine (&cr, 0);
	}
}

synthese_aff_neg (struct put_fnct *put, prop p, int aff)
{
int stack [15000];
	synthese_aff_neg1 (put, p, aff, stack+14950);
}
#endif
/*
	ameliorations :
		- phrases a plusieurs verbes : coroutine
		- prop neg
		- adverbes
			idee : verbe (action, sujet, COD)
				et adverbe (action)
				au lieu de verbe (sujet1, COD)
				et adverbe (sujet, sujet1)

	analyse

*/

char separ_mot[] = " ,\r\n\t";

char separ_prop[] = ";.?!";

int is_separ_mot (char c)
{
	if (strchr (separ_mot, c) == NULL)
		return 0;
	return 1;
}

int is_separ_prop (char c)
{
	if (strchr (separ_prop, c) == NULL)
		return 0;
	return 1;
}

#define DPS(arite,type,flag,nom1) \
	if (compare (nom, nom1)) \
		return predic (arite, type, flag, nom1);

pred pred_special (char *nom)
{
/*
	if (compare (nom, "mi"))
		return pred (1, PRED_NOM, FLAG_PRONOM, "mi");
*/
	DPS (1, PRED_NOM, FLAG_PRONOM, "mi")
	DPS (1, PRED_NOM, FLAG_PRONOM, "ci")
	DPS (1, PRED_NOM, FLAG_PRONOM | FLAG_MASCULIN, "li")
	DPS (1, PRED_NOM, FLAG_PRONOM | FLAG_FEMININ, "^si")
	DPS (1, PRED_NOM, FLAG_PRONOM | FLAG_NEUTRE, "^gi")
	DPS (1, PRED_NOM, FLAG_PRONOM | FLAG_PLURIEL, "ni")
	DPS (1, PRED_NOM, FLAG_PRONOM, "vi")
	DPS (1, PRED_NOM, FLAG_PRONOM | FLAG_PLURIEL, "ili")

	DPS (1, PRED_ADJ_PRE, FLAG_PRONOM, "mia")
	DPS (1, PRED_ADJ_PRE, FLAG_PRONOM, "cia")
	DPS (1, PRED_ADJ_PRE, FLAG_PRONOM | FLAG_MASCULIN, "lia")
	DPS (1, PRED_ADJ_PRE, FLAG_PRONOM | FLAG_FEMININ, "^sia")
	DPS (1, PRED_ADJ_PRE, FLAG_PRONOM | FLAG_NEUTRE, "^gia")
	DPS (1, PRED_ADJ_PRE, FLAG_PRONOM | FLAG_PLURIEL, "nia")
	DPS (1, PRED_ADJ_PRE, FLAG_PRONOM, "via")
	DPS (1, PRED_ADJ_PRE, FLAG_PRONOM | FLAG_PLURIEL, "ilia")

	/* DPS (1, PRED_SPECIAL, 0, "ne") */

	DPS (1, PRED_ART, 0, "la")

	DPS (2, PRED_PREP, 0, "al")
	DPS (2, PRED_PREP, 0, "anstataw")
	DPS (2, PRED_PREP, 0, "antaw")
	DPS (2, PRED_PREP, 0, "malantaw")
	DPS (2, PRED_PREP, 0, "apud")
	DPS (2, PRED_PREP, 0, "^ce")
	DPS (2, PRED_PREP, 0, "^cirkaw")
	DPS (2, PRED_PREP, 0, "ekster")
	DPS (2, PRED_PREP, 0, "dum")
	DPS (2, PRED_PREP, 0, "el")
	DPS (2, PRED_PREP, 0, "en")
	DPS (2, PRED_PREP, 0, "^gis")
	DPS (2, PRED_PREP, 0, "inter")
	DPS (2, PRED_PREP, 0, "kontraw")
	DPS (2, PRED_PREP, 0, "krom")
	DPS (2, PRED_PREP, 0, "kun")
	DPS (2, PRED_PREP, 0, "law")
	DPS (2, PRED_PREP, 0, "malgraw")
	DPS (2, PRED_PREP, 0, "per")
	DPS (2, PRED_PREP, 0, "por")
	DPS (2, PRED_PREP, 0, "post")
	DPS (2, PRED_PREP, 0, "preter")
	DPS (2, PRED_PREP, 0, "pri")
	DPS (2, PRED_PREP, 0, "pro")
	DPS (2, PRED_PREP, 0, "sen")
	DPS (2, PRED_PREP, 0, "sub")
	DPS (2, PRED_PREP, 0, "super")
	DPS (2, PRED_PREP, 0, "sur")
	DPS (2, PRED_PREP, 0, "tra")
	DPS (2, PRED_PREP, 0, "trans")

	DPS (1, PRED_NOM, FLAG_PRONOM, "iu")
	DPS (1, PRED_NOM, FLAG_PRONOM, "tiu")
	DPS (1, PRED_NOM, FLAG_PRONOM, "^ciu")
	DPS (1, PRED_NOM, FLAG_PRONOM, "neniu")

	DPS (1, PRED_ADV, FLAG_PRONOM, "iam")
	DPS (1, PRED_ADV, FLAG_PRONOM, "tiam")
	DPS (1, PRED_ADV, FLAG_PRONOM, "^ciam")
	DPS (1, PRED_ADV, FLAG_PRONOM, "neniam")

	DPS (1, PRED_ADV, FLAG_PRONOM, "iel")
	DPS (1, PRED_ADV, FLAG_PRONOM, "tiel")
	DPS (1, PRED_ADV, FLAG_PRONOM, "^ciel")
	DPS (1, PRED_ADV, FLAG_PRONOM, "neniel")

	DPS (1, PRED_ADV, FLAG_PRONOM, "ial")
	DPS (1, PRED_ADV, FLAG_PRONOM, "tial")
	DPS (1, PRED_ADV, FLAG_PRONOM, "^cial")
	DPS (1, PRED_ADV, FLAG_PRONOM, "nenial")

	DPS (1, PRED_ADV, FLAG_PRONOM, "iom")
	DPS (1, PRED_ADV, FLAG_PRONOM, "tiom")
	DPS (1, PRED_ADV, FLAG_PRONOM, "^ciom")
	DPS (1, PRED_ADV, FLAG_PRONOM, "neniom")

	DPS (1, PRED_ADJ_PRE, FLAG_PRONOM, "ies")
	DPS (1, PRED_ADJ_PRE, FLAG_PRONOM, "ties")
	DPS (1, PRED_ADJ_PRE, FLAG_PRONOM, "^cies")
	DPS (1, PRED_ADJ_PRE, FLAG_PRONOM, "nenies")

	DPS (2, PRED_PREP_ADJ, 0, "de")
	DPS (2, PRED_PREP_ADJ, 0, "da")
	DPS (2, PRED_PREP_ADJ, 0, "po")

	DPS (1, PRED_CONJ_NOM, FLAG_COORD | FLAG_ACTIF | FLAG_ACCUSATIF,
		"ke")

	DPS (1, PRED_CONJ/*ADJ*/, 0, "kiu")
	/* DPS (1, PRED_CONJ, FLAG_ACCUSATIF, "kiun") */

	if (compare (nom, "kaj"))
		return fin_prop;

	return NULL;
}

struct get_state
{
	char last_char;
	pred last_pred;
	obj last_object;
};

pred get_pred (struct get_fnct *get, struct get_state *state)
{
char nom[120];
int i;
char c;
pred p;
int flag;
	if (is_separ_prop (state->last_char))
	{
		state->last_char = ' ';
		return fin_prop;
	}
	flag = 0;
	do
		c = state->last_char = cget (get);
	while (is_separ_mot(c));
	if (is_separ_prop(c))
		return fin_prop;
	i = 0;
	do
	{
		nom[i++] = c;
		c = state->last_char = cget (get);
	}
	while (!is_separ_mot(c) && !is_separ_prop(c));
	nom[i] = 0;
boucle:
	p = pred_special (nom);
	if (p != NULL)
	{
		p->flags |= flag;
		return p;
	}
	switch (nom[i-1])
	{
		case 'o': /* nom */
			nom[i-1] = 0;
			p = predic (1, PRED_NOM, flag, stralloc(nom));
			break;

		case 'i': /* infinitif */
			flag |= FLAG_INFINITIF;
			nom[i-1] = 0;
			p = predic (1, PRED_NOM, flag, stralloc(nom));
			break;

		case 'a': /* adjectif */
			nom[i-1] = 0;
			p = predic (1, PRED_ADJ_PRE, flag, stralloc(nom));
			break;

		case 'e': /* adverbe */
			nom[i-1] = 0;
			p = predic (1, PRED_ADV, flag, stralloc(nom));
			break;

		case 's': /* verbe */
			c = nom[i-2];
			switch (c)
			{
				case 'a': flag |= FLAG_PRESENT; break;
				case 'i': flag |= FLAG_PASSE; break;
				case 'o': flag |= FLAG_FUTUR; break;
				case 'u': flag |= FLAG_CONDITIONNEL; break;
				default: goto autre;
			}
			nom[i-2] = 0;
			p = predic (3, PRED_VERB, flag, stralloc(nom));
			break;

		case 'u':
			flag |= FLAG_VOLITIF;
			nom[i-1] = 0;
			p = predic (3, PRED_VERB, flag, stralloc(nom));
			break;

		case 'n': /* accusatif */
			flag |= FLAG_ACCUSATIF;
			nom[i-1] = 0;
			i--;
			goto boucle;

		case 'j': /* pluriel */
			flag |= FLAG_PLURIEL;
			nom[i-1] = 0;
			i--;
			goto boucle;

		default:
		autre:
			flag |= FLAG_NOM_PROPRE;
			p = predic (1, PRED_NOM, flag, nom);

	}
	return p;
}

prop get_prop_1 (struct get_fnct *get, struct get_state *state,
	obj obj_action, prop action,
	obj obj_sujet, prop sujet,
	obj obj_cod, prop cod);

/* Lecture d'un groupe nominal :
	on lit une suite d'adjectifs et un seul nom tous au meme cas
*/

prop get_gn (struct get_fnct *get, struct get_state *state, obj objet)
{
int flag_accusatif, flag_nominatif;
int flag_nom_lu;
/*obj objet;*/
prop p, p1, c;
pred prep_adj, gn, objet1, conj;

	/*objet = new_var ();*/
	state->last_object = objet;

	if (state->last_pred->type == PRED_CONJ_NOM)
	{
			// conj = state->last_pred->type;
			conj = state->last_pred;
			state->last_pred = get_pred (get, state);
			if (conj->flags & FLAG_COORD)
				c = NULL;
			else
				c = ap1 (conj, objet);
			if (conj->flags & FLAG_ACTIF)
			{
				p1 = get_prop_1 (get, state,
					objet, c /*ap1 (conj, objet)*/,
					new_var(), NULL,
					new_var(), NULL);
			}
			else if (conj->flags & FLAG_ACCUSATIF)
			{
				p1 = get_prop_1 (get, state,
					new_var(), NULL,
					new_var(), NULL,
					objet, c /*NULL*/ /*ap1 (conj, objet)*/);
				/*p = and (p, p1);*/
			}
			else
			{
				p1 = get_prop_1 (get, state,
					new_var(), NULL,
					objet, c,
					new_var(), NULL);
				/*p = and (p, p1);*/
			}
			return p1;

	}

	if (state->last_pred->type == PRED_NOM)
		flag_nom_lu = 1;
	else
		flag_nom_lu = 0;
	/*
	if (state->last_pred->flags & FLAG_NOMINATIF)
		flag_nominatif = 1;
	else
		flag_nominatif = 0;
	*/
	if (state->last_pred->flags & FLAG_ACCUSATIF)
		flag_accusatif = 1;
	else
		flag_accusatif = 0;

	p = ap1 (state->last_pred, objet);
	state->last_pred = get_pred (get, state);

	for (;;)
	{
		if (state->last_pred->type == PRED_NOM)
		{
			if (flag_nom_lu)
				break;
			flag_nom_lu = 1;
		}
		else if (state->last_pred->type != PRED_ADJ_PRE &&
			 state->last_pred->type != PRED_ADJ_POST &&
			 state->last_pred->type != PRED_PREP_ADJ &&
			 state->last_pred->type != PRED_CONJ)
			break;

		if (state->last_pred->type == PRED_PREP_ADJ)
		{
			prep_adj = state->last_pred;
			state->last_pred = get_pred (get, state);
			objet1 = new_var ();
			gn = get_gn (get, state, objet1);
			p = and (p, and (ap2 (prep_adj, objet, objet1), gn));

		}
		else if (state->last_pred->type == PRED_CONJ)
		{
			conj = state->last_pred;
			state->last_pred = get_pred (get, state);
			if (conj->flags & FLAG_COORD)
				c = NULL;
			else
				c = ap1 (conj, objet);
			if (conj->flags & FLAG_ACTIF)
			{
				p1 = get_prop_1 (get, state,
					objet, c /*ap1 (conj, objet)*/,
					new_var(), NULL,
					new_var(), NULL);
			}
			else if (conj->flags & FLAG_ACCUSATIF)
			{
				p1 = get_prop_1 (get, state,
					new_var(), NULL,
					new_var(), NULL,
					objet, c /*NULL*/ /*ap1 (conj, objet)*/);
				/*p = and (p, p1);*/
			}
			else
			{
				p1 = get_prop_1 (get, state,
					new_var(), NULL,
					objet, c,
					new_var(), NULL);
				/*p = and (p, p1);*/
			}
			p = and (p, p1);

		}
		else
		{
		    if ((!flag_accusatif &&
				(state->last_pred->flags & FLAG_ACCUSATIF))||
			 (flag_accusatif &&
				!(state->last_pred->flags & FLAG_ACCUSATIF)))
			 break;
		    else
		    {
			p = and (p, ap1 (state->last_pred, objet));
			state->last_pred = get_pred (get, state);
		    }
		}
	}
	return p;
}


/* Lecture d'un groupe verbal :
	on lit une suite d'adverbes et un seul verbe
*/

prop get_gv (struct get_fnct *get, struct get_state *state,
	obj action, obj sujet, obj cod)
{
int flag_verbe_lu;
/*obj action;*/
prop p;

	/*action = new_var ();*/
	state->last_object = action;

	switch (state->last_pred->type)
	{
		case PRED_VERB:
			flag_verbe_lu = 1;
			p = ap3 (state->last_pred, action, sujet, cod);
			break;
		case PRED_ADV:
			flag_verbe_lu = 0;
			p = ap1 (state->last_pred, action);
			break;
		default:
			return NULL;
	}

	state->last_pred = get_pred (get, state);

	for (;;)
	{
		if (state->last_pred->type == PRED_VERB)
		{
			if (flag_verbe_lu)
				break;
			flag_verbe_lu = 1;
		}
		else if (state->last_pred->type != PRED_ADV)
			break;


		    switch (state->last_pred->type)
		    {
			case PRED_VERB:
			    flag_verbe_lu = 1;
			    p = and (p,
				ap3 (state->last_pred, action, sujet, cod));
			    break;
			case PRED_ADV:
			    p = and (p, ap1 (state->last_pred, action));
			    break;
			default:
			    return NULL;
		    }

		state->last_pred = get_pred (get, state);

	}
	return p;
}

/* Lecture d'une proposition : (ordre variable)
	1 groupe nominal au nominatif (article, adjectifs, 1 nom)
	1 groupe verbal (adverbes, 1 verbe)
	1 groupe nominal a l'accusatif
	complements = preposition groupe nominal au nominatif
*/

#define MAX_COMPLEMENTS 30


prop get_prop (struct get_fnct *get, struct get_state *state)
{
pred preposition[MAX_COMPLEMENTS], prep;
int flag_defini, flag_accusatif, flag_complement;
prop gn, action, sujet, verbe, cod, complement[MAX_COMPLEMENTS], compl;
int n_complements;
obj obj_action, obj_sujet, obj_cod, obj_complement[MAX_COMPLEMENTS], obj_compl;
prop p, d;

	obj_action = new_var ();
	obj_sujet = new_var ();
	obj_cod = new_var ();
	action = sujet = cod = NULL;

	p = get_prop_1 (get, state,
		obj_action, action, obj_sujet, sujet, obj_cod, cod);

	return p;
}

prop get_prop_1 (struct get_fnct *get, struct get_state *state,
	obj obj_action, prop verbe,
	obj obj_sujet, prop sujet, obj obj_cod, prop cod)
{
pred preposition[MAX_COMPLEMENTS], prep;
int flag_defini, flag_accusatif, flag_complement;
prop gn, /*sujet,*/ /*verbe,*/ /*cod,*/ complement[MAX_COMPLEMENTS], compl;
int n_complements;
obj /*action,*/ /*obj_sujet, obj_cod,*/
	obj_complement[MAX_COMPLEMENTS], obj_compl;
prop p, d;

	p = NULL;
	n_complements = 0;
	flag_defini = 0;
	/* state->last_pred = get_pred (get, state); */
	/* action = new_var (); */
	/*
	obj_sujet = new_var ();
	obj_cod = new_var ();
	sujet = cod = NULL;
	*/
	/*verbe = NULL;*/

    for (;;)
    {
	if (state->last_pred == fin_prop)
	{
		return p;
	}

	if (state->last_pred->type == PRED_PREP)
	{
		n_complements++;
		preposition[n_complements-1] = prep = state->last_pred;
		obj_complement[n_complements-1] = obj_compl = new_var ();
		state->last_pred = get_pred (get, state);
		flag_complement = 1;
	}
	else
		flag_complement = 0;

	if (state->last_pred->type == PRED_ART)
	{
		if (compare (state->last_pred->name, "la"))
			flag_defini = 1;
		else
			flag_defini = 0;
		state->last_pred = get_pred (get, state);
	}
	else
		flag_defini = 0;

	/* if (state->last_pred->type != TYPE_NOM &&
	 *	state->last_pred->type != TYPE_ADJ)
	 *		return NULL;
	 */

	d = NULL;

	switch (state->last_pred->type)
	{
		/*case TYPE_ART:*/
		case PRED_ART:
		case PRED_PREP:
			/* return NULL; */
			return p;

		case PRED_NOM:
		case PRED_CONJ_NOM:
		case PRED_ADJ_PRE:
		case PRED_ADJ_POST:
			if (flag_complement)
			{
			    complement[n_complements-1] = compl =
				get_gn (get, state, obj_compl);
					/*obj_complement[n_complements-1]);*/
			    if (flag_defini)
				d = ap1 (pred_defini, obj_compl);

			    p = and (p, and (d,
				and (ap2 (prep, obj_action, obj_compl), compl)));
			}
			else if (state->last_pred->flags & FLAG_ACCUSATIF)
			{
				flag_accusatif = 1;
				if (cod != NULL)
					return p; /* NULL */
				if (flag_defini)
					d = ap1 (pred_defini, obj_cod);
				cod = and (d, get_gn (get, state, obj_cod));
				p = and (p, cod);
			}
			else
			{
				flag_accusatif = 0;
				if (sujet != NULL)
					return p; /* NULL */
				if (flag_defini)
					d = ap1 (pred_defini, obj_sujet);
				sujet = and (d,
					get_gn (get, state, obj_sujet));
				p = and (p, sujet);
			}
			break;

		case PRED_VERB:
		case PRED_ADV:
			if (verbe != NULL)
				return p;
			verbe = get_gv (get, state,
					obj_action, obj_sujet, obj_cod);
			p = and (p, verbe);
			break;

		case PRED_SPECIAL:

			break;
		default:
			return p /*NULL*/;
	}
    }

}

prop analyse (struct get_fnct *get)
{
struct get_state state[1];
prop p;
	trace ("analyse", 0);
	state->last_char = ' ';
	state->last_pred = get_pred (get, state);
	trace ("get_prop...", 0);
	p = get_prop (get, state);
	trace ("return analyse", 0);
	return p;
}

main ()
{
/* struct perso_info perso; */
FILE *in_file, *out_file;
struct param_file param_in, param_out;
struct get_fnct get_in;
struct put_fnct put_out;
char question[1000], reponse[1000];
int statut;
prop p;
struct get_state state[1];

	printf ("LANGUAGE=%d\n", LANGUAGE);

    printf ("Initialisation\n");

    param_in.fd = stdin;
    param_out.fd = stdout;

    get_in.f = f_get_file;
    get_in.p = &param_in;

    put_out.f = f_put_file;
    put_out.p = &param_out;

    /* init_perso (&perso, &get_in, &put_out); */

    p = example1 ();
    synthese (&put_out, p);

    state->last_char = ' ';

    /* for (;;) */
    /*
    {
	p = get_pred (&get_in, state);
	print_pred (p);
    }
    */

    printf ("\n");
    for (;;)
    {
    trace ("analyse...", 0);
    p = analyse (&get_in);
    trace ("synthese...", 0);
    synthese (&put_out, p);
    trace ("au revoir", 0);
    sput (&put_out, "\n");
    }

    /*
    for (;;)
    {
	sput (&put_out, "\n? ");
	sget (&get_in, question);
	if (!*question)
		break;
	repondre (&perso, question, reponse);
	sput (&put_out, "> ");
	sput (&put_out, reponse);
    }
    */


}



