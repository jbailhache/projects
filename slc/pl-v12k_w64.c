// Proof Logic by Jacques Bailhache (jacques.bailhache@gmail.com) 
// Compilation : cc -g -fno-stack-protector -o pl-v12 pl-v12.c schedule.c
//  For global table of proofs, add option "-DGLOBAL" (do not use with coroutines)
//  To modifiy default maximum number of proof, add option "-DMAXPROOFS=n"
//  Example : cc -g -fno-stack-protector -DGLOBAL -DMAXPROOFS=200000 -o pl-v12 pl-v12.c schedule.c

#define SIDES

#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "schedule_w64.h"

struct coroutine calling[1];

int use_coroutines;

int print_help (char *progname) {
	printf("\n");
	printf("Usage: %s [OPTIONS] [FILE]\n",progname);
	printf("\n");
	printf("Options:\n");
	printf(" -a : use coroutines\n");
	printf(" -c : displays only conclusion, not reduction\n");
	printf(" -f : full reduction\n");
	printf(" -g : use coroutines to compute the conclusion of \"a = b ; c = d\" with the 4 possibilities (a = c, b = c, a = d, b = d) \n");
	printf(" -h : display this help\n");
	printf(" -o : occur-check\n");
	printf(" -q : quiet mode\n");
	printf(" -Q : read file without echo\n");
	printf(" -r : print reduction of proofs read from file\n");
	printf(" -u : display only value of unknown\n");
	printf(" -U : use coroutines when matching \"_\" with 2 possibilities : it matches or it does not match \n");
	printf("\n");
	printf("After starting the program, a prompt \"?\" is displayed. Type a proof ended by \".\", or just \".\" to quit. The reduction and the conclusion of this proof is displayed. \n");
	printf("\n");
	printf("A proof is one of the following (where x and y are proofs) :\n");
	printf(" A name represented by a sequence of characters not associated with an operator and with no particular syntactic meaning\n");
	printf(" *     : the first variable (De Bruijn index)\n");
	printf(" 'x    : the next variable (De Bruijn index)\n");
	printf(" [x]   : a function \n");
	printf(" x y   : application \n");
	printf(" x ; y : generalized transitivity\n");
	printf(" x = y : equality axiom\n");
	printf(" @ x   : pre-reduction (reduce before deducing)\n");
	printf(" $ x   : post-reduction (reduce the conclusion)\n");
	printf(" / x   : one step of reduction of left part of conclusion\n");
	printf(" \\ x   : one step of reduction of right part of conclusion\n");
	printf(" - x   : full reduction of right part of conclusion operator\n");
	printf(" ` x   : search for matching proof for transitivity\n");
	printf(" ? x y : print x and conclusion of y\n");
	printf(" x | y : use coroutines to compute its conclusion with 2 possibilities : the conclusion of x or the conclusions of y \n");
	printf(" < x   : reduces to left part of conclusion of x\n");
	printf(" > x   : reduces to right part of conclusion of x\n");
	printf(" 1 x   : reduces to first operand of x\n");
	printf(" 2 x   : reduces to second operand of x\n");
	printf(" x , y : use coroutines to reduce it with 2 possibilities : x or y\n");
	printf("\n");
	printf("Syntactic constructs :\n");
	printf(" ( : )   : syntactic grouping\n");
	printf(" ! x y z : let x = y in z\n");
	printf(" %% x y z : let x = y in z and print the result\n");
	printf(" & x y   : give name x to y\n");
	printf(" { x y   : give name x to y\n");
	printf(" } x     : copy of x\n");
	printf(" + x     : print full definition of x\n");
	printf(" ~ x     : reads the reduction of x\n");
	printf(" \"filename.prf\" : loads a file\n");
	printf(" # ...   : comment\n");
	printf("\n");
	printf("Special characters ordered by ASCII code :\n");
	printf(" ! x y z : let x = y in z\n");
	printf(" \"filename.prf\" : loads a file\n");
	printf(" # ...   : comment\n");
	printf(" $ x     : post-reduction operator\n");
	printf(" %% x y z : let x = y in z and print the result\n");
	printf(" & x y   : give name x to y\n");
	printf(" ' x     : next variable operator\n");
	printf(" ( ... ) : syntactic grouping\n");
	printf(" *       : first variable\n");
	printf(" + x     : print full definition of x\n");
	printf(" x , y   : use coroutines to reduce it with 2 possibilities : x or y\n");
	printf(" - x     : full reduction of right part of conclusion operator\n");
	printf(" .       : end of proof, quit\n");
	printf(" / x     : one step of reduction of left part of conclusion operator\n");
	printf(" :       : syntactic grouping\n");
	printf(" x ; y   : generalized transitivity operator\n");
	printf(" < x     : reduces to left part of conclusion of x\n");
	printf(" x = y   : equality axiom operator\n");
	printf(" > x     : reduces to right part of conclusion of x\n");
	printf(" ? x y   : rint x and conclusion of y operator\n");
	printf(" @ x     : pre-reduction operator\n");
	printf(" [x]     : function operator\n");
	printf(" \\ x     : one step of reduction of right part of conclusion operator\n");
	printf(" ^x y    : lambda expression\n");
	printf(" _       : unknown\n");
	printf(" ` x     : search for matching proof for transitivity\n");
	printf(" { x y   : give name x to y\n");
	printf(" } x     : copy of x\n");
	printf(" x | y   : use coroutines to compute its conclusion with 2 possibilities : the conclusion of x or the conclusions of y \n");
	printf(" ~ x     : reads the reduction of x\n");
	printf("\n");
}

int pof () {
	///printf("\nPOF");
	if (!use_coroutines) 
		return 1;
	if (alt(calling, (void *)1, (void *)0)) {
		///printf("\nPOF 1");
		return 1;
	} else {
		///printf("\nPOF 0");
		return 0;
	}
}

int pof_end () {
	///printf("\nPOF");
	if (!use_coroutines) 
		return 1;
	if (alt(calling, (void *)1, (void *)0)) {
		///printf("\nPOF 1");
		return 1;
	} else {
		///printf("\nPOF 0");
		//return 0;
		end(calling);
	}
}

/* INPUT - OUTPUT */

int quiet_read;
int occur_check;
int full_red;
int print_value_of_unknown;
int gtr_alt;
int unknown_alt;
int use_sides;

struct reader {
	char (*getchar)(struct reader *);
	void *p;
};

char getchar_from_reader (struct reader *reader) {
	char c;
	c = (*(reader->getchar))(reader);
	return c;
}


char getchar_from_string (struct reader *reader) {
	char c;
	c = *(char *)(reader->p);
	*(char *)reader->p++;
	return c;
}

void read_from_string (struct reader *reader, char *s) {
	reader->getchar = getchar_from_string;
	reader->p = s;
}


char getchar_from_stdin (struct reader *reader) {
	return getchar();
}

void read_from_stdin (struct reader *reader) {
	reader->getchar = getchar_from_stdin;
}


char getchar_from_file (struct reader *reader) {
	char c;
	c = fgetc((FILE *)(reader->p));
	if (!quiet_read && c != 0 && c != 0xFF && c != -1) printf("%c",c);
	return c;
}

void read_from_file (struct reader *reader, FILE *f) {
	reader->getchar = getchar_from_file;
	reader->p = f;
}


struct printer {
	void (*putchar)(struct printer *,char);
	void *p;
};

void putchar_to_printer (struct printer *printer, char c) {
	(*(printer->putchar))(printer, c);
}

void putstring_to_printer (struct printer *printer, char *s) {
	while (*s) {
		putchar_to_printer(printer, *s++);
	}
}


void putchar_to_string (struct printer *printer, char c) {
	*(char *)(printer->p)++ = c;
}

void print_to_string (struct printer *printer, char *s) {
	printer->putchar = putchar_to_string;
	printer->p = s;
}


void putchar_to_stdout (struct printer *printer, char c) {
	putchar(c);
}

void print_to_stdout (struct printer *printer) {
	printer->putchar = putchar_to_stdout;
}


void putchar_to_file (struct printer *printer, char c) {
	fputc(c, (FILE *)(printer->p));
}

void print_to_file (struct printer *printer, FILE *f) {
	printer->putchar = putchar_to_file;
	printer->p = f;
}


/* OPERATORS */

#define LEFT  0
#define RIGHT 1

#define SMB 'a'
#define ANY '_'
#define VAR '*'
#define NXV '\''
#define FNC '['
#define RED '@'
#define RLR '$'
#define APL ' '
#define GTR ';'
#define EQU '='
#define RSL '/'
#define RSR '\\'
#define RRR '-'
#define PRT '?'

#define LFT '<'
#define RGT '>'
#define SP1 '1'
#define SP2 '2'

// #define RFE '`'
#define RET '`'

//#define FPR '+'

#define ALT '|'
#define ALR ','

struct oper {
	char code;
	int arity;
};

// Operators with standard prefixed syntax
struct oper operators[] = {
	{ NXV, 1 }, 
	{ RED, 1 },
	{ RLR, 1 },
	{ RSL, 1 },
	{ RSR, 1 },
	{ RRR, 1 },
	{ PRT, 2 },
	{ LFT, 1 },
	{ RGT, 1 },
	{ SP1, 1 },
	{ SP2, 1 },
	{ RET, 1 }
// ,{ RFE, 1 }
// ,{ FPR, 1 }
};	

#define N_OPERATORS (sizeof(operators)/sizeof(operators[0]))

#define NOCERT 0.0

typedef struct proof1 *proof;

#define NAMESIZE 31

struct proof1 {
	int op;
	double cert;
	char name[NAMESIZE+1];
	proof sp1, sp2, red, side[2], val;	
};

#ifndef MAXPROOFS
#ifdef GLOBAL
#define MAXPROOFS 100000
#else
//#define MAXPROOFS 20000
#define MAXPROOFS 5000
#endif
#endif

int nproofs;

//struct proof1 proofs[MAXPROOFS];
struct proof1 *proofs;

void print_proof_to_stdout (proof x);
void print_full_proof_to_stdout (proof x);

void copy_proof (proof src, proof dst) {
	dst->op = src->op;
	dst->cert = src->cert;
	dst->sp1 = src->sp1;
	dst->sp2 = src->sp2;
	dst->red = src->red;
	dst->side[0] = src->side[0];
	dst->side[1] = src->side[1];
	dst->val = src->val;
}

void init() {
	nproofs = 0;
	proofs[nproofs].op = VAR;
	proofs[nproofs].red = proofs+nproofs;
	proofs[nproofs].side[LEFT] = proofs+nproofs;
	proofs[nproofs].side[RIGHT] = proofs+nproofs;
	proofs[nproofs].val = NULL;
	proofs[nproofs].cert = NOCERT;
	proofs[nproofs].name[0] = 0;
	nproofs++;	
}

//proof var = proofs;
proof var;

void check_memory() {
	if (nproofs >= MAXPROOFS) {
		printf("Memory overflow\n");
		exit(1);
	}	
	proofs[nproofs].sp1 = NULL;
	proofs[nproofs].sp2 = NULL;
	proofs[nproofs].red = NULL;
	proofs[nproofs].side[LEFT] = NULL;
	proofs[nproofs].side[RIGHT] = NULL;
	proofs[nproofs].val = NULL;
	proofs[nproofs].cert = NOCERT;
}

proof any() {
	check_memory();
	proofs[nproofs].op = ANY;
	proofs[nproofs].val = NULL;
	return proofs+nproofs++;
}

proof smb(char *name) {
	int i;
	for (i=0; i<nproofs; i++) {
		if (proofs[i].op == SMB && !strcmp(proofs[i].name,name)) {
			return proofs+i;
		}
	}
	check_memory();
	proofs[nproofs].op = SMB;
	proofs[nproofs].val = NULL;
	strcpy(proofs[nproofs].name,name);
	return proofs+nproofs++;
}
	
proof proof_with_name (char *name) {
	int i;
	for (i=0; i<nproofs; i++) {
		if (!strcmp(proofs[i].name,name)) {
			return proofs+i;
		}
	}
	check_memory();
	proofs[nproofs].op = SMB;
	proofs[nproofs].val = NULL;
	strcpy(proofs[nproofs].name,name);
	return proofs+nproofs++;
}

proof copy_of_proof (proof src) {
	proof dst;
	check_memory();
	dst = proofs+nproofs;
	copy_proof(src,dst);
	nproofs++;
	return dst;
}

proof empty_proof;

#define DEFOP1(o,f) \
proof f(proof x) { \
	int i; \
	for (i=0; i<nproofs; i++) { \
		if (proofs[i].op == o && proofs[i].sp1 == x) \
			return proofs+i; \
	} \
	check_memory(); \
	if (x == NULL) x = empty_proof; \
	proofs[nproofs].op = o; \
	proofs[nproofs].sp1 = x; \
	proofs[nproofs].sp2 = NULL; \
	proofs[nproofs].val = NULL; \
	return proofs+nproofs++; \
}

DEFOP1(NXV,nxv)
DEFOP1(FNC,fnc)
DEFOP1(RED,red)
DEFOP1(RLR,rlr)
DEFOP1(RSL,rsl)
DEFOP1(RSR,rsr)
DEFOP1(RRR,rrr)

DEFOP1(LFT,lft)
DEFOP1(RGT,rgt)
DEFOP1(SP1,sp1)
DEFOP1(SP2,sp2)

DEFOP1(RET,ret)

//DEFOP1(RFE,rfe)
//DEFOP1(FPR,fpr)

#define DEFOP2(o,f) \
proof f(proof x, proof y) { \
	int i; \
	for (i=0; i<nproofs; i++) { \
		if (proofs[i].op == o && proofs[i].sp1 == x && proofs[i].sp2 == y) \
			return proofs+i; \
	} \
	check_memory(); \
	if (x == NULL) x = empty_proof; \
	if (y == NULL) y = empty_proof; \
	proofs[nproofs].op = o; \
	proofs[nproofs].sp1 = x; \
	proofs[nproofs].sp2 = y; \
	proofs[nproofs].val = NULL; \
	return proofs+nproofs++; \
}

DEFOP2(APL,apl)
DEFOP2(GTR,gtr)
DEFOP2(EQU,equ)
DEFOP2(PRT,prt)
DEFOP2(ALT,alp)
DEFOP2(ALR,alr)

int eq (proof x, proof y);

proof mkproof(int op, proof x, proof y) { 
	int i; 
	for (i=0; i<nproofs; i++) { 
		if (proofs[i].op == op && proofs[i].sp1 == x && proofs[i].sp2 == y) 
			return proofs+i; 
	} 
	check_memory(); 
	proofs[nproofs].op = op; 
	proofs[nproofs].sp1 = x; 
	proofs[nproofs].sp2 = y; 
	proofs[nproofs].val = NULL;
	return proofs+nproofs++; 
}


/* REDUCTION */

// shift(u,x) increases all variables greater than u in x
proof shift (proof u, proof x) {
	if (x == u) return nxv(x);
	if (x == NULL) return x;
	switch (x->op) {
		case SMB :
			return x;
		case ANY :
			return x;
		case VAR :
			return x;
		case FNC :
			return fnc(shift(nxv(u),x->sp1));
		default :
			return mkproof(x->op,shift(u,x->sp1),shift(u,x->sp2));
	}
}

proof subst (proof u, proof a, proof b) {
	if (u == a) return b;
	if (a == NULL) return a;
	if (a->op == NXV && a->sp1 == u) return u;
	switch (a->op) {
		case SMB :
		case VAR :
		case ANY :
			return a;
		case FNC :
			return fnc(subst(nxv(u),a->sp1,shift(var,b)));
		default :
			return mkproof(a->op, subst(u, a->sp1, b), subst(u, a->sp2, b));
	}
}

// x contains y ?
int cont (proof x, proof y) {
	if (x == y)
		return 1;
	if (x == NULL)
		return 0;
	if (x->val != NULL & cont(x->val, y))
		return 1;
	switch (x->op) {
		case SMB :
		case VAR :
		case ANY :
			return 0;
		default :
			return cont(x->sp1, y) || cont(x->sp2, y);
	}
}

int contsp (proof x, proof y) {
	if (cont(x,y)) return 1;
	if (full_red) return 0;
	if (x == NULL) return 0;
	if (y == NULL) return 0;
	if (x->op != y->op) return 0;
	return contsp(x->sp1,y->sp1) && contsp(x->sp2,y->sp2);
}


proof left(proof x);
proof right(proof x);

proof reduce (proof x);

/*proof reduce1 (proof x) {
	proof l, r;
	if (x == NULL) return x;
	if (x->op == SMB) return x;
	if (x->op == ANY) return x;
	if (x->op == APL && x->sp1->op == FNC)
		return subst(var, x->sp1->sp1, x->sp2);
	if (x->op == LFT)
		return left(reduce(x->sp1));
	if (x->op == RGT)
		return right(reduce(x->sp1));
	if (x->op == SP1)
		return reduce(x->sp1)->sp1;
	if (x->op == SP2)
		return reduce(x->sp1)->sp2;
	//if (x->op == FPR) {
	//	printf("\nFull definition of proof : ");
	//	print_proof_to_stdout(x->sp1);
	//	printf("\n                      is : ");
	//	print_full_proof_to_stdout(x->sp1);
	//}
	if (x->op == FNC && x->sp1->op == APL && x->sp1->sp2->op == VAR) 
		return x->sp1->sp1;
	if (x->op == ALR) {
		if (pof()) {
			return x->sp1;
		} else {
			return x->sp2;
		}
	}
	return mkproof(x->op, reduce1(x->sp1), reduce1(x->sp2));
}*/
			
proof reduce1step (proof x) {
	proof l, r, y;
	if (x == NULL) return x;
	if (x->op == SMB) return x;
	if (x->op == ANY) return x;
	if (x->op == APL && x->sp1->op == FNC)
		return subst(var, x->sp1->sp1, x->sp2);
	if (x->op == LFT)
		return left(reduce(x->sp1));
	if (x->op == RGT)
		return right(reduce(x->sp1));
	if (x->op == SP1)
		return reduce(x->sp1)->sp1;
	if (x->op == SP2)
		return reduce(x->sp1)->sp2;
	/*if (x->op == FPR) {
		printf("\nFull definition of proof : ");
		print_proof_to_stdout(x->sp1);
		printf("\n                      is : ");
		print_full_proof_to_stdout(x->sp1);
	}*/
	if (x->op == FNC && x->sp1->op == APL && x->sp1->sp2->op == VAR) 
		return x->sp1->sp1;
	if (x->op == ALR) {
		if (pof()) {
			return x->sp1;
		} else {
			return x->sp2;
		}
	}
	y = reduce1step(x->sp1);
	if (!eq(y,x->sp1)) {
		return mkproof(x->op, y, x->sp2);
	} else {
		y = reduce1step(x->sp2);
		return mkproof(x->op, x->sp1, y);
	}
}	

proof reduce1 (proof x) {
	return reduce1step(x);
}

#define MAX 10000

proof reduce2 (proof x) {
	proof y, z;
	proof a[MAX];
	int n, i, found;
	if (x == NULL) return x;
	n = 0;
	y = x;
	for (;;)
	{
		a[n++] = y;
		z = reduce1(y);
		if (n >= MAX) break;
		found = 0;
		for (i=0; i<n; i++) {
			if (contsp(z,a[i])) {
				found = 1;
				break;
			} 
		}
		if (found) return y;
		y = z;
	}
	return z;
}

proof reduce3 (proof x) {
	proof y, z;
	proof a[MAX];
	int n, i, found;
	int nsteps;
	if (x == NULL) return x;
	n = 0;
	y = x;
	nsteps = 0;
	for (;;)
	{
		nsteps++;
		a[n++] = y;
		z = reduce1step(y);
		//printf("\n\t %d : ", nsteps);
		//print_proof_to_stdout(z);
		if (n >= MAX) break;
		found = 0;
		for (i=0; i<n; i++) {
			if (eq(z,a[i])) {
				found = 1;
				break;
			} 
		}
		if (found) {
			printf("\n%d steps",nsteps);
			return y;
		}
		y = z;
	}
	printf("\n%d steps",nsteps);
	return z;
}

proof reduce (proof x) {
	proof y;
	if (x == NULL) return x;
	if (x->red != NULL) return x->red;
	x->red = x;
	y = reduce2(x);
	x->red = y;
	return y;
}

int eq (proof x, proof y) {
	int p;
	//printf("\nCompare : ");
	//print_proof_to_stdout(x);
	//printf("\nand     : ");
	//print_proof_to_stdout(y);
	if (x == y) {
		//printf("\nEqual\n");
		return 1;
	}
	if (x == NULL || y == NULL) return 0;
	if (x->op == ANY) {
		if (x->val == NULL) {
			if (unknown_alt) {
				p = pof();
				//printf("\np = %d", p);
			}
			if ((!occur_check || !cont(y,x)) && (!unknown_alt || p)) {
				x->val = y;
				//printf("\nAssign to ");
				if (!print_value_of_unknown) {
					printf("\n");
					print_proof_to_stdout(x);
				}
				//printf(" the value ");
				//print_proof_to_stdout(y);
				//printf("\n");
				return 1;
			} else {
				return 0;
			}
		} else {
			return eq(x->val, y);
		}
	}
	if (y->op == ANY) {
		if (y->val == NULL) {
			if (unknown_alt) {
				p = pof();
				//printf("\np = %d",p);
			}
			if ((!occur_check || !cont(x,y)) && (!unknown_alt || p)) {
				y->val = x;
				//printf("\nAssign to ");
				if (!print_value_of_unknown) {
					printf("\n");
					print_proof_to_stdout(y);
				}
				//printf(" the value ");
				//print_proof_to_stdout(x);
				//printf("\n");
				return 1;
			} else {
				return 0;
			}
		} else {
			return eq(x, y->val);
		}
	}
	if (x->op != y->op) {
		//printf("\nDifferent operators\n");
		return 0;
	}
	if (x->op == SMB) {
		//printf("\nDifferent symbols\n");
		return 0;
	}
	if (!eq(x->sp1,y->sp1)) return 0;
	if (!eq(x->sp2,y->sp2)) return 0;
	return 1;
}

int eqr (proof x, proof y) {
	return 
		eq(x,y) ||
		eq(x,reduce(y)) ||
		eq(reduce(x),y) ||
		eq(reduce(x),reduce(y));
}

/*int eqr (proof x, proof y) {
	return 
		x == y ||
		x == reduce(y) ||
		reduce(x) == y ||
		reduce(x) == reduce(y);
}*/


/* CONCLUSION */

proof side (int s, proof x);
proof left (proof x);
proof right (proof x);

proof side1 (int s, proof x) {
	proof y, z, a, b;
	int i, n;
int p, q;
    ///printf("\n---calculate side %d of ",s);
    ///print_proof_to_stdout(x);
	if (x == NULL) return NULL;
	///printf("\nop=%c",x->op);
	switch (x->op) {
		case SMB :
			return x;
		case ANY :
			return x;
		case EQU : 
			switch(s) {
				case LEFT  :  return x->sp1;
				case RIGHT : return x->sp2;
				default    : return NULL;
			}
		case RED :
			return side(s,reduce(x->sp1));
		case RLR :
			return reduce(side(s,x->sp1));
		case RSL :
			switch(s) {
				case LEFT  : return reduce1(side(s,x->sp1));
				case RIGHT : return side(s,x->sp1);
				default    : return NULL;
			}
		case RSR :
			switch(s) {
				case LEFT  : return side(s,x->sp1);
				case RIGHT : return reduce1(side(s,x->sp1));
				default    : return NULL;
			}
		case RRR :
			switch(s) {
				case LEFT  : return side(s,x->sp1);
				case RIGHT : return reduce3(side(s,x->sp1));
				default    : return NULL;
			}
		//case LFT :
		//	return side(LEFT,x->sp1);
		//case RGT :
		//	return side(RIGHT,x->sp1);
		case GTR :
			///printf("\nGTR");
			p = 1;
			q = 1;
			if (gtr_alt) {
				p = pof();
			}
			if (p || !use_coroutines || !gtr_alt) {
				if (gtr_alt) {
					q = pof();
				}
				if (q || !use_coroutines || !gtr_alt) {
				//if (pof()) {
				//if (pof()) {
					if (eqr(left(x->sp1),left(x->sp2)) /*&& pof()*/) {
						///printf("\nleft = left side %d", s);
						switch(s) {
							case LEFT  : return right(x->sp1);
							case RIGHT : return right(x->sp2);
							default    : return NULL;
						}
					}
					///printf("\nleft != left");
				}
				if (!q || !use_coroutines || !gtr_alt) {
				//} else {
					if (eqr(right(x->sp1),left(x->sp2)) /*&& pof()*/) {
						///printf("\nright = left side %d", s);
						switch(s) {
							case LEFT  : return left(x->sp1);
							case RIGHT : return right(x->sp2);
							default    : return NULL;
						}
					}
					///printf("\nright != left");
				}
			}
			if (!p || !use_coroutines || !gtr_alt) {
				if (gtr_alt) {
					q = pof();
				}
				if (q || !use_coroutines || !gtr_alt) {
				//}
				//} else {
				//if (pof()) {
					if (eqr(left(x->sp1),right(x->sp2)) /*&& pof()*/) {
						///printf("\nleft = right side %d", s);
						switch(s) {
							case LEFT  : return right(x->sp1);
							case RIGHT : return left(x->sp2);
							default    : return NULL;
						}
					}
					///printf("\nleft != right");
				}
				if (!q || !use_coroutines || !gtr_alt) {
				//} else {
					if (eqr(right(x->sp1),right(x->sp2)) /*&& pof()*/) {
						///printf("\nright = right side %d", s);
						switch(s) {
							case LEFT  : return left(x->sp1);
							case RIGHT : return left(x->sp2);
							default    : return NULL;
						}
					}
					///printf("\nright != right");
				}
			}
			if (use_coroutines) {
				///printf("\nGTR : no match, end");
				end(calling);
			} else {
				return x;
			}
		case PRT :
			y=side(s,x->sp2);
			switch(s) {
				case LEFT  : printf("\nLeft  of "); break;
				case RIGHT : printf("Right of "); break;
				default    : ;
			}
			print_proof_to_stdout(x->sp1);
			printf(" is : ");
			print_proof_to_stdout(y);
			printf("\n");
			return y;
		/*case FPR :
			y = side(s, x->sp1);
			printf("\nFull definition of proof : ");
			print_proof_to_stdout(y);
			printf("\n                      is : ");
			print_full_proof_to_stdout(y);
			return y;*/
		//case RFE :
		//	return equ(left(x->sp1),right(x->sp1));
		case RET :
			//printf("\nRetrieve      : ");
			//print_proof_to_stdout(x->sp1);
			n = nproofs;
			for (i=0; i<n; i++) {
				y = proofs+i;
				if (y != x) {
					//printf("\nProof %d",i);
					//printf("\nTry with      : ");
					//print_proof_to_stdout(y);
					//z = gtr(x->sp1,y);
					z = gtr(side(s,x->sp1),y);
					//printf("\nConclusion of : ");
					//print_proof_to_stdout(z);
					a = left(z);
					//printf("\nis            : ");
					//print_proof_to_stdout(a);
					b = right(z);
					//printf("\nequals        : ");
					//print_proof_to_stdout(b);
					if (a != z && b != z && a != b) {
						//printf("\nFound");
						switch(s) {
							case LEFT  : return a;
							case RIGHT : return b;
							default    : ;
						}
					}
					//printf("\n");
				}
			}
			//printf("\nNot found");
			return x->sp1;
		case ALT :
			if (pof()) {
				return side(s,x->sp1);
			} else {
				return side(s,x->sp2);
			}
		default :
			y = mkproof(x->op, side(s,x->sp1), side(s,x->sp2));
			// y->cert = cert(x->sp1) * cert(x->sp2);
			return y;
	}
}

void sides (proof x, proof *l, proof *r) {
	proof y, z, a, b, l1, r1, l2, r2, zl, zr;
	int i, n;
	int p, q;
	///printf("\ncalculate sides of ");
	///print_proof_to_stdout(x);
	if (x == NULL) {
		*l = NULL;
		*r = NULL;
		return;
	}
	switch (x->op) {
		case SMB :
			if (use_coroutines && !strcmp(x->name,"END")) {
				end(calling);
			}
		case ANY :
			*l = x;
			*r = x;
			return;
		case EQU : 
			*l = x->sp1;
			*r = x->sp2;
			return;
		case RED :
			sides(reduce(x->sp1),l,r);
			return;
		case RLR :
			sides(x->sp1,l,r);
			*l = reduce(*l);
			*r = reduce(*r);
			return;
		case RSL :
			sides(x->sp1,&l1,&r1);
			*l = reduce1(l1);
			*r = r1;
			return;
		case RSR :
			sides(x->sp1,&l1,&r1);
			*l = l1;
			*r = reduce1(r1);
			return;
		case RRR :
			sides(x->sp1,&l1,&r1);
			*l = l1;
			*r = reduce3(r1);
			return;
		//case LFT :
		//	return side(LEFT,x->sp1);
		//case RGT :
		//	return side(RIGHT,x->sp1);
		case GTR :
			sides(x->sp1,&l1,&r1);
			sides(x->sp2,&l2,&r2);
			p = 1;
			q = 1;
			if (gtr_alt) {
				p = pof();
			} 
			if (p || !use_coroutines || !gtr_alt) {
				if (gtr_alt) {
					q = pof();
				}
				if (q || !use_coroutines || !gtr_alt) {
				//if (pof()) {
				//if (pof()) {
					if (eqr(l1,l2)) {
						*l = r1;
						*r = r2;
						return;
					}
				}
				if (!q || !use_coroutines || !gtr_alt) {
				//} else {
					if (eqr(r1,l2)) {
						*l = l1;
						*r = r2;
						return;
					}
				}
			}
			if (!p || !use_coroutines || !gtr_alt) {
				if (gtr_alt) {
					q = pof();
				}
				if (q || !use_coroutines || !gtr_alt) {
				//}
				//} else {
				//if (pof()) {
					if (eqr(l1,r2)) {
						*l = r1;
						*r = l2;
						return;
					}
				}
				if (!q || !use_coroutines || !gtr_alt) {
				//} else {
					if (eqr(r1,r2)) {
						*l = l1;
						*r = l2;
						return;
					}
				}		
			}
			if (use_coroutines) {
				///printf("\nGTR : no match, end");
				end(calling);
			} else {
				*l = x;
				*r = x;
				return;
			}
			
		case PRT :
			sides(x->sp2,l,r);
			printf("\nLeft  of ");
			print_proof_to_stdout(x->sp1);
			printf(" is : ");
			print_proof_to_stdout(*l);
			printf("\n");
			printf("\nRight of ");
			print_proof_to_stdout(x->sp1);
			printf(" is : ");
			print_proof_to_stdout(*r);
			printf("\n");
			return;
		/*case FPR :
			y = side(s, x->sp1);
			printf("\nFull definition of proof : ");
			print_proof_to_stdout(y);
			printf("\n                      is : ");
			print_full_proof_to_stdout(y);
			return y;*/
		//case RFE :
		//	return equ(left(x->sp1),right(x->sp1));
		case RET :
			//printf("\nRetrieve      : ");
			//print_proof_to_stdout(x->sp1);
			n = nproofs;
			for (i=0; i<n; i++) {
				y = proofs+i;
				if (y != x) {
					//printf("\nProof %d",i);
					//printf("\nTry with      : ");
					//print_proof_to_stdout(y);
					//z = gtr(x->sp1,y);
					// z = gtr(side(s,x->sp1),y);				
					sides(x->sp1,&l1,&r1);
					zl = gtr(l1,y);
					zr = gtr(r1,y);	
					//printf("\nConclusion of : ");
					//print_proof_to_stdout(z);
					a = left(zl);
					//printf("\nis            : ");
					//print_proof_to_stdout(a);
					b = right(zr);
					//printf("\nequals        : ");
					//print_proof_to_stdout(b);
					if (a != zl && b != zr && a != b) {
						//printf("\nFound");
						*l = a;
						*r = b;
						return;
					}
					//printf("\n");
				}
			}
			//printf("\nNot found");
			*l = x->sp1;
			*r = x->sp1;
			return;
		case ALT :
			if (pof()) {
				sides(x->sp1, l, r);
			} else {
				sides(x->sp2, l, r);
			}
			return; 
		default :
			//y = mkproof(x->op, side(s,x->sp1), side(s,x->sp2));
			sides(x->sp1,&l1,&r1);
			sides(x->sp2,&l2,&r2);
			*l = mkproof(x->op,l1,l2);
			*r = mkproof(x->op,r1,r2);
			return;
			// y->cert = cert(x->sp1) * cert(x->sp2);
			//return y;
	}
}

proof side (int s, proof x) {
	int i;
    ///printf("\nside %d of ",s);
    ///print_proof_to_stdout(x);
	if (x == NULL)
		return x;
//#ifndef SIDES
	if (!use_sides) {
		for (i=LEFT; i==LEFT||i==RIGHT; i+=RIGHT-LEFT) {
			///printf(" i=%d",i);
			if (x->side[i] == NULL) {
				///printf(" NULL");
				x->side[i] = x;
				x->side[i] = side1(i,x);
			}
		}
//#else
	} else {
		if (x->side[LEFT] == NULL || x->side[RIGHT] == NULL) {
			x->side[LEFT] = x;
			x->side[RIGHT] = x;
			sides(x,&(x->side[LEFT]),&(x->side[RIGHT]));
		}
	}
//#endif
    ///printf(" sides calculated");
	return x->side[s];
}
	
proof left (proof x) {
	return side(LEFT,x);
}

proof right (proof x) {
	return side(RIGHT,x);
}


/* CERTAINTY (FUZZY LOGIC) */

double cert (proof x);

/*double cert1 (proof x) {
	if (x == NULL) return 1;
	if (x->cert == NOCERT) return 1.0;
	return x->cert;
}*/

double cert (proof x) {
double c1, c2;
	//printf ("\ncertainty of ");
	//print_proof_to_stdout(x);
	//printf ("\nsp1 = ");
	//print_proof_to_stdout(x->sp1);
	//printf("\nsp2 = ");
	//print_proof_to_stdout(x->sp2);
	if (x == NULL) return 1.0;
	if (x->cert == NOCERT) {
		// x->cert = cert(x->sp1) * cert(x->sp2);
		// return cert(x->sp1) * cert(x->sp2);
		x->cert = 1.0;
		//x->cert = cert(x->sp1) * cert(x->sp2);
		c1 = cert(x->sp1);
		c2 = cert(x->sp2);
		x->cert = c1 * c2;
	}
	//printf (" is %lf\n",x->cert);
	return x->cert;
}


/* ABSTRACTION */

proof abstr (proof u, proof v, proof x) {
	if (v == x) return u;
	if (!cont(x,v)) return x;
	if (x == NULL) return x;
	if (x->op == FNC) 
		return fnc(abstr(nxv(u),v,x->sp1));
	return mkproof(x->op, abstr(u,v,x->sp1), abstr(u,v,x->sp2));
}

proof lambda (proof v, proof x) {
	if (x->op == APL && x->sp2 == v && !cont(x->sp1,v)) return x->sp1; // ^x (f x) = f
	return fnc(abstr(var,v,x));
}


/* READING PROOFS */

#define NLEVEL 100

int level = 0;

struct reader readers[NLEVEL];


int cur_char;

int nextchar (struct reader *reader) {
	cur_char = getchar_from_reader(reader);
	//printf(" %02X%c ", cur_char, cur_char);
	if (cur_char == '#') {
		while (cur_char != '\n' && cur_char != -1) {
			cur_char = getchar_from_reader(reader);
		}
	} else if (cur_char == '"') {
		char filename[100];
		int i = 0;
		FILE *f;
		cur_char = getchar_from_reader(reader);
		while (cur_char != '"' && cur_char != -1) {
			filename[i++] = cur_char;
			cur_char = getchar_from_reader(reader);
		}
		cur_char = getchar_from_reader(reader);
		filename[i] = 0;
		f = fopen(filename,"r");
		if (f == NULL) {
			printf("\nCannot open file %s\n", filename);
			return nextchar(reader);
		} else {
			readers[level].getchar = reader->getchar;
			readers[level].p = reader->p;
			level++;
			read_from_file(reader,f);
			return nextchar(reader);
		}
	} else if ((cur_char == -1 || cur_char == 0xFF) && level > 0) {
		level--;
		reader->getchar = readers[level].getchar;
		reader->p = readers[level].p;
		return nextchar(reader);
	} else {
		return cur_char;
	}
}

void skip_blanks(struct reader *reader) {
	while (cur_char != 0 && cur_char != 255 && strchr(" \t\n\r",cur_char)) 
		nextchar(reader);
}

void read_name (struct reader *reader, char *name) {
	int i;
	i = 0;
	for (;;) {
		if (i > NAMESIZE) break;
		if (!cur_char) break;
		// if (cur_char == 0 || cur_char == -1 || strchr(" \t\n\r()*'\\[]-/%{,}<|>#=;.",cur_char)) break;
		// if (cur_char == 0 || cur_char == -1 || strchr(" \t\n\r()*'\\[]/%<>#=;.",cur_char)) break;
		if (cur_char == 0 || cur_char == -1 || strchr(" \t\n\r()[]#=;|,.}",cur_char)) break;
		name[i++] = cur_char;
		nextchar(reader);
	}
	name[i] = 0;
}

proof read_proof_2 (struct reader *reader, int options);
// options :
//  1 : returnv [*] if nothing to read, otherwise return NULL

proof read_proof_1 (struct reader *reader) {
	char c;
	proof x, y, z, l, r, a[2];
	char name[32];
	int i, j;
	char buf[100];
	double cert;
	skip_blanks(reader);
	switch(cur_char) {
		case 0 :
		case -1 :
		case 255 :
			return smb("NULL");
		case '_' :
			nextchar(reader);
			return any();
		case '*' :
			nextchar(reader);
			return var;
		/*case '-' :
			nextchar(reader);
			x = read_proof_1(reader);
			y = read_proof_1(reader);
			//return apl(x,y);
			return y;*/
		case '(' :
			nextchar(reader);
			x = read_proof_2(reader, 1);
			if (cur_char == ')')
				nextchar(reader);
			return x;
		case '[' :
			nextchar(reader);
			x = read_proof_2(reader, 1);
			if (cur_char == ']')
				nextchar(reader);
			return fnc(x);
		case '^' :
			nextchar(reader);
			x = read_proof_1(reader);
			y = read_proof_1(reader);
			return lambda(x,y);
		case '!' :
			nextchar(reader);
			x = read_proof_1(reader);
			y = read_proof_1(reader);
			z = read_proof_1(reader);
			return red(apl(lambda(x,z),y));
		case '%' :
			nextchar(reader);
			x = read_proof_1(reader);
			y = read_proof_1(reader);
			z = read_proof_1(reader);
			return red(apl(lambda(x,z),prt(x,y)));
		case '&' :
		case '{' :
			nextchar(reader);
			skip_blanks(reader);
			read_name(reader,name);
			x = read_proof_1(reader);
			for (i=0; i<nproofs; i++) {
				if (!strcmp(proofs[i].name,name)) {
					//printf("\nAnother proof has the name \"%s\".\n", name);
					//return x;
					copy_proof(x, proofs+i);
					return proofs+i;
				}
			}
			strncpy(x->name, name, NAMESIZE);
			return x;
		case '+' :
			nextchar(reader);
			x = read_proof_1(reader);
			printf("\nFull definition of proof : ");
			print_proof_to_stdout(x);
			printf("\n                      is : ");
			print_full_proof_to_stdout(x);
			printf("\n");
			return x;
		case '~' :
			nextchar(reader);
			x = read_proof_1(reader);
			return reduce(x);
		case '}' :
			nextchar(reader);
			x = read_proof_1(reader);
			return copy_of_proof(x);
		default :
			//if (cur_char >= '0' && cur_char <= '9') {
			if (cur_char == '0') {
				i = 0;
				while ((cur_char >= '0' && cur_char <= '9') || cur_char == '.') {
					buf[i++] = cur_char;
					nextchar(reader);
				}
				buf[i] = 0;
				sscanf(buf,"%lf",&cert);
				x = read_proof_1(reader);
				x->cert = cert;
				return x;
			}
			for (i=0; i<N_OPERATORS; i++) {
				if (operators[i].code == cur_char) {
					nextchar(reader);
					a[0] = NULL;
					a[1] = NULL;
					for (j=0; j<operators[i].arity; j++) {
						a[j] = read_proof_1(reader);
					}
					return mkproof(operators[i].code, a[0], a[1]);
				}
			}		
			read_name(reader,name);
			//return smb(name);			
			return proof_with_name(name);
	}
}

proof sequ (proof x, proof y) {
	if (x == NULL) return y;
	if (y == NULL) return x;
	return equ(x,y);
}

proof sgtr (proof x, proof y) {
	if (x == NULL) return y;
	if (y == NULL) return x;
	return gtr(x,y);
}

proof salt (proof x, proof y) {
	if (x == NULL) return y;
	if (y == NULL) return x;
	return alp(x,y);
}

proof salr (proof x, proof y) {
	if (x == NULL) return y;
	if (y == NULL) return x;
	return alr(x,y);
}

struct infix_op {
	int op;
	char c;
	proof (*f)(proof,proof);
};

struct infix_op infix_ops[] = { 
	{ ALR, ',', alr },
	{ EQU, '=', equ },
	{ GTR, ';', gtr },
	{ ALT, '|', alp }
};

proof siop (int i, proof x, proof y) {
	if (x == NULL) return y;
	if (y == NULL) return x;
	return (*(infix_ops[i].f))(x,y);
}

int n_infix_ops = sizeof(infix_ops)/sizeof(infix_ops[0]);
proof read_proof_2 (struct reader *reader, int options) {
	//proof x, y, z, t, u, v, r;
	proof y, z, r;
	proof a[n_infix_ops];
	int i, j;
	int op_found;
	a[0] = NULL;
	y = NULL;
	a[1] = NULL;
	a[2] = NULL;
	a[3] = NULL;
	/*for (i=0; i<n_infix_ops; i++) {
		a[i] = NULL;
	}*/
	for (;;) {
		skip_blanks(reader);
		switch(cur_char) {
			case 0 :
			case -1 :
			case 255 :
			case ')' :
			case ']' :
			//case ',' :
			//case '}' :
			//case '|' :
			//case '>' :
			case '.' :
				// r = sgtr(t,sequ(x,y));
				// r = salt(u,sgtr(t,sequ(x,y)));
				// r = salr(v,salt(u,sgtr(t,sequ(x,y))));
				// r = salr(a[3],salt(a[2],sgtr(a[1],sequ(a[0],y))));
				r = y;
				for (i=0; i<n_infix_ops; i++) {
					//printf("\ni=%d r : ",i);
					//print_proof_to_stdout(r);
					//printf("\na[i] : ");
					//print_proof_to_stdout(a[i]);
					//if (a[i] == NULL) printf (" NULL");
					//r = (*(infix_ops[i].f))(a[i],r);
					r = siop(i,a[i],r);
					//printf("\ni=%d r : ",i);
					//print_proof_to_stdout(r);
				}
				if (r == NULL && (options & 1)) return empty_proof;
				return r;
			/*case '=' :
				nextchar(reader);
				//a[0] = sequ(a[0],y);
				a[0] = y;
				for (j=0; j<=0; j++) {
					a[0]= siop(j,a[j],a[0]);
				}
				y = NULL;
				break;
			case ';' :
				nextchar(reader);
				//a[1] = sgtr(a[1],sequ(a[0],y));
				a[1] = y;
				for (j=0; j<=1; j++) {
					a[1]= siop(j,a[j],a[1]);
				}
				//a[0] = NULL;
				y = NULL;
				for (j=0; j<1; j++) {
					a[j] = NULL;
				}
				break;
			case '|' :
				nextchar(reader);
				//a[2] = salt(a[2],sgtr(a[1],sequ(a[0],y)));
				a[2] = y;
				for (j=0; j<=2; j++) {
					a[2]= siop(j,a[j],a[2]);
				}
				//a[0] = NULL;
				y = NULL;
				//a[1] = NULL;
				for (j=0; j<2; j++) {
					a[j] = NULL;
				}
				break;
			case ',':
				nextchar(reader);
				//a[3] = salr(a[3],salt(a[2],sgtr(a[1],sequ(a[0],y))));
				a[3] = y;
				for (j=0; j<=3; j++) {
					a[3] = siop(j,a[j],a[3]);
				}
				//a[0] = NULL;
				y = NULL;
				//a[1] = NULL;
				//a[2] = NULL;
				for (j=0; j<3; j++) {
					a[j] = NULL;
				}
				break;*/
			case ':' :
				nextchar(reader);
				z = read_proof_2(reader, 1);
				if (y == NULL) y = z;
				else y = apl(y,z);
				break;
			default :
				op_found = 0;
				for (i=0; i<n_infix_ops; i++) {
					if (cur_char == infix_ops[i].c) {
						op_found = 1;

						nextchar(reader);
						// v = salr(v,salt(u,sgtr(t,sequ(x,y))));
						r = y;
						for (j=0; j<=i; j++) {
							r = siop(j,a[j],r); 
						}
						a[i] = r;
						// x = NULL;
						y = NULL;
						// t = NULL;
						// u = NULL;
						for (j=0; j<i; j++) {
							a[j] = NULL;
						}


					}
				}
				if (!op_found) {
					z = read_proof_1(reader);
					if (y == NULL) y = z;
					else y = apl(y,z);
				}
		}
	}
}

proof read_proof_from_string (char *s) {
	struct reader reader;
	read_from_string(&reader,s);
	nextchar(&reader);
	return read_proof_2(&reader, 0);
}

proof read_proof_from_stdin () {
	struct reader reader;
	read_from_stdin(&reader);
	nextchar(&reader);
	return read_proof_2(&reader, 0);
}

proof read_proof_from_file (FILE *f) {
	struct reader reader;
	read_from_file(&reader, f);
	nextchar(&reader);
	return read_proof_1(&reader);
}

proof read_proof_from_file_2 (FILE *f) {
	struct reader reader;
	read_from_file(&reader, f);
	nextchar(&reader);
	return read_proof_2(&reader, 0);
}


/* PRINTING PROOFS */

void print_proof_1(struct printer *printer, proof x, int parenthesized, int full) {
	char buf[100];
	int i, j;
	int op;
	int op_found;
	if (x == NULL) {
		putstring_to_printer(printer, "0");
		return;
	}
	op = x->op;
	x->op = SMB;
	if (x->cert != NOCERT && x->cert != 1.0) {
		sprintf(buf,"%5.3lf (",x->cert);
		putstring_to_printer(printer, buf);
	}
	// 3 code lines below :
	// - commented : display full proof
	// - uncommented : display only name if the proof has a name
	if (!full && x->name[0]) {
		putstring_to_printer(printer, x->name);
	} else
	switch(op) {
		case SMB :
			putstring_to_printer(printer, x->name);
			break;
		case ANY :
			/*sprintf(buf, "_%lx", (long)x);
			putstring_to_printer(printer, buf);
			if (x->val != NULL) {
				putstring_to_printer(printer, "=");
				print_proof_1(printer,x->val,0,full);
			}*/
			if (!(print_value_of_unknown && x->val != NULL)) {
				putstring_to_printer(printer, "_");
			}
			break;
		case VAR :
			putstring_to_printer(printer, "*");
			break;
		case FNC :
			putstring_to_printer(printer, "[");
			print_proof_1(printer, x->sp1, 0, full);
			putstring_to_printer(printer, "]");
			break;
		case APL :
			if (parenthesized & 2) putstring_to_printer(printer, "(");
			print_proof_1(printer, x->sp1, 5, full);
			putstring_to_printer(printer, " ");
			print_proof_1(printer, x->sp2, 7, full);
			if (parenthesized & 2) putstring_to_printer(printer, ")");
			break;
		/*case GTR : 
			if (parenthesized & 4) putstring_to_printer(printer, "( ");
			print_proof_1(printer, x->sp1, 4, full);
			putstring_to_printer(printer, " ; ");
			print_proof_1(printer, x->sp2, 4, full);
			if (parenthesized & 4) putstring_to_printer(printer, " )");			
			break;
		case EQU :
			if (parenthesized & 1) putstring_to_printer(printer, "(");
			print_proof_1(printer, x->sp1, 1, full);
			putstring_to_printer(printer, " = ");
			print_proof_1(printer, x->sp2, 1, full);
			if (parenthesized & 1) putstring_to_printer(printer, ")");
			break;
		case ALT :
			if (parenthesized & 1) putstring_to_printer(printer, "(");
			print_proof_1(printer, x->sp1, 1, full);
			putstring_to_printer(printer, " | ");
			print_proof_1(printer, x->sp2, 1, full);
			if (parenthesized & 1) putstring_to_printer(printer, ")");
			break;
		case ALR :
			if (parenthesized & 1) putstring_to_printer(printer, "(");
			print_proof_1(printer, x->sp1, 1, full);
			putstring_to_printer(printer, " , ");
			print_proof_1(printer, x->sp2, 1, full);
			if (parenthesized & 1) putstring_to_printer(printer, ")");
			break;*/
		default :
			op_found = 0;
			for (i=0; i<n_infix_ops; i++) {
				if (op == infix_ops[i].op) {
					op_found = 1;

					if (parenthesized & 1) putstring_to_printer(printer, "(");
					print_proof_1(printer, x->sp1, 1, full);
					sprintf(buf," %c ",infix_ops[i].c);
					putstring_to_printer(printer, buf);
					print_proof_1(printer, x->sp2, 1, full);
					if (parenthesized & 1) putstring_to_printer(printer, ")");

				}
			}
			if (!op_found) {
				sprintf(buf,"%c", op);
				putstring_to_printer(printer, buf);
				for (i=0; i<N_OPERATORS; i++) {
					if (operators[i].code == op) {
						if (operators[i].arity > 0) {
							print_proof_1(printer, x->sp1, 7, full);
							if (operators[i].arity > 1) {
								putstring_to_printer(printer, " ");
								print_proof_1(printer, x->sp2, 7, full);
							}
						}
					}
				}
			}					
	}
	if (x->val != NULL) {
		proof v;
		v = x->val;
		x->val = NULL;
		if (print_value_of_unknown && v != NULL && !(!full && x->name[0])) {
			print_proof_1(printer,v,3,full);
		} else {
			putstring_to_printer(printer, "{");
			print_proof_1(printer,v,0,full);
			putstring_to_printer(printer, "}");
		}
		x->val = v;
	}
	if (x->cert != NOCERT && x->cert != 1.0) {
		putstring_to_printer(printer, ")");
	}
	x->op = op;
}
		
void print_proof_to_stdout (proof x) {
	struct printer printer;
	print_to_stdout(&printer);
	print_proof_1(&printer,x,0,0);
}

void print_full_proof_to_stdout (proof x) {
	struct printer printer;
	print_to_stdout(&printer);
	print_proof_1(&printer,x,0,1);
}

void read_file (char *filename, char *buf) {
	int c;
	FILE *f;
	f = fopen(filename,"r");
	if (f == NULL) {
		printf("Cannot open file %s\n", filename);
		exit(1);
	}
	for (;;) {
		c = fgetc(f);
		if (c == EOF) break;
		*buf++ = c;
	}
	*buf++ = 0;
	fclose(f);
}


/* TOPLEVEL */

char filename[1000];
int quiet;
int print_red;
int conclusion_only;

void init_args (int argc, char *argv[]) {
	strcpy(filename, "");
	quiet = 0;
	print_red = 0;
	quiet_read = 0;
	occur_check = 0;
	full_red = 0;
	conclusion_only = 0;
	print_value_of_unknown = 0;
    use_coroutines = 0;
	gtr_alt = 0;
	unknown_alt = 0;
	use_sides = 1;
	if (argc > 1) {
		if (argv[1][0] == '-') {
			if (argc > 2) strcpy(filename, argv[2]);
            if (strchr(argv[1],'h')) {
                print_help(argv[0]);
                exit(0);
            }
			if (strchr(argv[1],'q')) quiet = 1;
			if (strchr(argv[1],'Q')) quiet_read = 1;
			if (strchr(argv[1],'r')) print_red = 1;
			if (strchr(argv[1],'o')) occur_check = 1;
			if (strchr(argv[1],'f')) full_red = 1;
			if (strchr(argv[1],'c')) conclusion_only = 1;
			if (strchr(argv[1],'u')) print_value_of_unknown = 1;
			if (strchr(argv[1],'a')) use_coroutines = 1;
			if (strchr(argv[1],'g')) gtr_alt = 1;
			if (strchr(argv[1],'U')) unknown_alt = 1;
			if (strchr(argv[1],'s')) use_sides = 0;
		} else {
			strcpy(filename, argv[1]);
		}
	}
	//printf("\nuse_coroutines = %d\n",use_coroutines);
}

#ifdef GLOBAL
struct proof1 proofs_buf[MAXPROOFS];
#endif

// int main (int argc, char *argv[]) {
void *maincr1 (void *p, struct coroutine *c1)
{	
	char buf[10000];
	proof x, y, l, r;
	FILE *f;
	// char *filename;
	// int quiet;
	// int print_red;
	// int conclusion_only;
	struct reader reader;
	long i;
	long z;
	
	if (use_coroutines) {
		memcpy (calling, c1, sizeof(calling));
	}

#ifndef GLOBAL
	struct proof1 proofs_buf[MAXPROOFS];
#endif
	proofs = proofs_buf;
	var = proofs;

	init();
	empty_proof = fnc(var);
	//filename = NULL;
	/*strcpy(filename, "");
	quiet = 0;
	print_red = 0;
	quiet_read = 0;
	occur_check = 0;
	full_red = 0;
	conclusion_only = 0;
	print_value_of_unknown = 0;
    use_coroutines = 0;

	if (argc > 1) {
		if (argv[1][0] == '-') {
			if (argc > 2) filename = argv[2];
			if (strchr(argv[1],'q')) quiet = 1;
			if (strchr(argv[1],'Q')) quiet_read = 1;
			if (strchr(argv[1],'r')) print_red = 1;
			if (strchr(argv[1],'o')) occur_check = 1;
			if (strchr(argv[1],'f')) full_red = 1;
			if (strchr(argv[1],'c')) conclusion_only = 1;
			if (strchr(argv[1],'u')) print_value_of_unknown = 1;
		} else {
			filename = argv[1];
		}
	}*/
	
	if (filename[0]) {
		f = fopen(filename, "r");
		if (f == NULL) {
			printf("\nCannot open file %s.\n", filename);
			exit(1);
		}
		read_from_file(&reader, f);
		for (;;) {
		  //if (pof()) {
			// x = read_proof_from_file_2(f);
			nextchar(&reader);
			x = read_proof_2(&reader, 0);
			if (x == NULL) break;
			if (print_red) {
				y = reduce(x);
			}
			l = left(x);
			r = right(x);
			if (!quiet) {
				printf("\nThe proof  : ");
				print_proof_to_stdout(x);
				if (print_red) {
					printf("\nreduces to : ");
					print_proof_to_stdout(y);				
					printf("\nand proves : ");
				} else {
					printf("\nproves     : ");
				}
				print_proof_to_stdout(l);
				printf("\nequals     : ");
				print_proof_to_stdout(r);
				if (cert(x) != NOCERT && cert(x) != 1.0) {
					printf("\ncertainty  : ");
					printf("%5.3f",cert(x));
				}
				printf("\n");
			}
			/*if (use_coroutines) {
				///printf("\nMain loop : end");
				end(calling);
			}*/
		  //}
		}
		printf("\n");
		fclose(f);
		return 0;
	}

	printf("Welcome to Proof Logic !\n");
	printf("Type a proof ended by \".\", and type just \".\" to quit.\n");
	read_from_stdin(&reader);

	/*for (i=1; i<10; i++)
	{
	  if (pof()) {
		printf ("i=%ld\n", i);
		if (i%2 == 0) end(calling);
		z = (long) alt (calling, (void *)(i*10+1), (void *)(i*10+2));
		printf ("z = %ld\n", z);	
		end (calling);
	  }
	}
	exit(0);*/

	for (;;) {
	  //if (pof()) {
		printf("\n? ");
		// x = read_proof_from_stdin();
		nextchar(&reader);
		x = read_proof_2(&reader, 0);
		//printf("\nproof read");
		if (x == NULL) break;
		//printf("\nThe proof  : ");
		//print_proof_to_stdout(x);
		//printf("\nfull_red=%d conclusion_only=%d", full_red, conclusion_only);
		if (!full_red && !conclusion_only) {
		//if (!full_red) {
			y = reduce(x);
			//printf ("\nreduces to : ");
			//print_proof_to_stdout(y);
		} /*else {
			printf("\nDo not print reduction");
		}*/
		///printf ("\nCalculate left and right");
		l = left(x);
		///printf ("\nLeft  = ");
		///print_proof_to_stdout(l);
		r = right(x);
		///printf("\nRight = ");
		///print_proof_to_stdout(r);
		//sides(x,&l,&r);
		printf("\nThe proof  : ");
		print_proof_to_stdout(x);
		if (!full_red && !conclusion_only) {
			printf ("\nreduces to : ");
			print_proof_to_stdout(y);
			printf ("\nand proves : ");
		} else {
			printf ("\nproves     : ");
		}
		// printf ("\nproves     : ");
		print_proof_to_stdout(l);
		printf ("\nequals     : ");
		print_proof_to_stdout(r);
		if (cert(x) != NOCERT && cert(x) != 1.0) {
			printf ("\ncertainty  : ");
			printf("%5.3f",cert(x));
		}
		printf("\n");
		/*if (use_coroutines) {
			///printf("\nMain loop : end");
			end(calling);
		}*/
	  //}
	}
	exit(0);
}

void *maincr (void *p, struct coroutine *c1)
{
	char buf[100000];
	proof x, y, l, r;
	FILE *f;
	// char *filename;
	// int quiet;
	// int print_red;
	// int conclusion_only;
	struct reader reader;
	long i;
	long z;
	double c;

	//printf("Debut maincr\n");	
	
	if (use_coroutines) {
		memcpy (calling, c1, sizeof(calling));
	}

	struct proof1 proofs_buf[MAXPROOFS];
	proofs = proofs_buf;
	var = proofs;

	init();
	empty_proof = fnc(var);
	//filename = NULL;
	
	if (filename[0]) {
		f = fopen(filename, "r");
		if (f == NULL) {
			printf("\nCannot open file %s.\n", filename);
			exit(1);
		}
		read_from_file(&reader, f);
		for (;;) {
		  //if (pof()) {
			// x = read_proof_from_file_2(f);
			nextchar(&reader);
			x = read_proof_2(&reader, 0);
			if (x == NULL) break;
			if (print_red) {
				y = reduce(x);
			}
			l = left(x);
			r = right(x);
			if (!quiet) {
				printf("\nThe proof  : ");
				print_proof_to_stdout(x);
				if (print_red) {
					printf("\nreduces to : ");
					print_proof_to_stdout(y);				
					printf("\nand proves : ");
				} else {
					printf("\nproves     : ");
				}
				print_proof_to_stdout(l);
				printf("\nequals     : ");
				print_proof_to_stdout(r);
				if (cert(x) != NOCERT && cert(x) != 1.0) {
					printf("\ncertainty  : ");
					printf("%5.3f",cert(x));
				}
				printf("\n");
			}
		  //}
		}
		printf("\n");
		fclose(f);
		return 0;
	}

	printf("Welcome to Proof Logic !\n");
	printf("Type a proof ended by \".\", and type just \".\" to quit.\n");
	read_from_stdin(&reader);

	for (;;) {
	  //if (pof()) {
		printf("\n? ");
		// x = read_proof_from_stdin();
		nextchar(&reader);
		x = read_proof_2(&reader, 0);
		//printf("\nproof read");
		if (x == NULL) break;
		//printf("\nThe proof  : ");
		//print_proof_to_stdout(x);
		//printf("\nfull_red=%d conclusion_only=%d", full_red, conclusion_only);
		if (!full_red && !conclusion_only) {
		//if (!full_red) {
			y = reduce(x);
			//printf ("\nreduces to : ");
			//print_proof_to_stdout(y);
		} 
		///printf ("\nCalculate left and right");
		l = left(x);
		///printf ("\nLeft  = ");
		///print_proof_to_stdout(l);
		r = right(x);
		///printf("\nRight = ");
		///print_proof_to_stdout(r);
		//sides(x,&l,&r);
		printf("\nThe proof  : ");
		print_proof_to_stdout(x);
		if (!full_red && !conclusion_only) {
			printf ("\nreduces to : ");
			print_proof_to_stdout(y);
			printf ("\nand proves : ");
		} else {
			printf ("\nproves     : ");
		}
		// printf ("\nproves     : ");
		print_proof_to_stdout(l);
		printf ("\nequals     : ");
		print_proof_to_stdout(r);
		//c = cert(x);
		if (cert(x) != NOCERT && cert(x) != 1.0) {
			printf ("\ncertainty  : ");
			printf("%5.3f",cert(x));
		}
		printf("\n");
		
	  //}
	}
	exit(0);
	
	//printf("Fin maincr\n");
}


/*void *maincr (void *p, struct coroutine *c1)
{
struct coroutine calling[1];
long x;
	memcpy (calling, c1, sizeof(calling));

	printf("Test\n");
	x = (long) alt (calling, (void *)111, (void *)222);
	printf ("x = %ld\n", x);	
	end (calling);
}*/

int main (int argc, char *argv[])
{
int stack [200000];
void *maincr ();
struct param_scheduler p;
	//printf("Test Debut\n");
	init_args(argc, argv);
	p.stack_size = sizeof(stack)-STACK_BOTTOM*sizeof(int);
	
	//printf("Welcome to Proof Logic !\n");
	//printf("Type a proof ended by \".\", and type just \".\" to quit.\n");
	if (use_coroutines) {
		scheduler (maincr, &p, stack, p.stack_size, 0);
	} else {
		maincr(NULL, NULL);
	}
	
	//printf("Test Fin\n");
}

int main1 (int argc, char *argv[])
{
	printf("Test\n");
}
