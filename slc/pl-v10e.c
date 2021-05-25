/* Proof Logic by Jacques Bailhache (jacques.bailhache@gmail.com) */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>


/* INPUT - OUTPUT */

int quiet_read;

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
#define APL '-'
#define GTR ';'
#define EQU '='
#define RSL '/'
#define RSR '\\'
#define PRT '?'

#define LFT '<'
#define RGT '>'
#define SP1 '1'
#define SP2 '2'

#define RFE '`'

//#define FPR '+'

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
	{ PRT, 2 },
	{ LFT, 1 },
	{ RGT, 1 },
	{ SP1, 1 },
	{ SP2, 1 },
	{ RFE, 1 }
//,{ FPR, 1 }
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

#define MAXPROOFS 100000

int nproofs;

struct proof1 proofs[MAXPROOFS];

void print_proof_to_stdout (proof x);
void print_full_proof_to_stdout (proof x);

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

proof var = proofs;

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

DEFOP1(LFT,lft)
DEFOP1(RGT,rgt)
DEFOP1(SP1,sp1)
DEFOP1(SP2,sp2)

DEFOP1(RFE,rfe)

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
	if (x == NULL) return 0;
	if (y == NULL) return 0;
	if (x->op != y->op) return 0;
	return contsp(x->sp1,y->sp1) && contsp(x->sp2,y->sp2);
}


proof left(proof x);
proof right(proof x);

proof reduce (proof x);

proof reduce1 (proof x) {
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
	/*if (x->op == FPR) {
		printf("\nFull definition of proof : ");
		print_proof_to_stdout(x->sp1);
		printf("\n                      is : ");
		print_full_proof_to_stdout(x->sp1);
	}*/
	if (x->op == FNC && x->sp1->op == APL && x->sp1->sp2->op == VAR) 
		return x->sp1->sp1;
	return mkproof(x->op, reduce1(x->sp1), reduce1(x->sp2));
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

proof reduce (proof x) {
	proof y;
	if (x == NULL) return x;
	if (x->red != NULL) return x->red;
	y = reduce2(x);
	x->red = y;
	return y;
}

int eq (proof x, proof y) {
	//printf("\nCompare : ");
	//print_proof_to_stdout(x);
	//printf("\nand     : ");
	//print_proof_to_stdout(y);
	if (x == y) {
		//printf("\nEqual\n");
		return 1;
	}
	if (x->op == ANY) {
		if (x->val == NULL) {
			x->val = y;
			//printf("\nAssign to ");
			printf("\n");
			print_proof_to_stdout(x);
			//printf(" the value ");
			//print_proof_to_stdout(y);
			//printf("\n");
			return 1;
		} else {
			return eq(x->val, y);
		}
	}
	if (y->op == ANY) {
		if (y->val == NULL) {
			y->val = x;
			//printf("\nAssign to ");
			printf("\n");
			print_proof_to_stdout(y);
			//printf(" the value ");
			//print_proof_to_stdout(x);
			//printf("\n");
			return 1;
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
	proof y, z;
	if (x == NULL) return NULL;
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
		//case LFT :
		//	return side(LEFT,x->sp1);
		//case RGT :
		//	return side(RIGHT,x->sp1);
		case GTR :
			if (eqr(left(x->sp1),left(x->sp2))) {
				switch(s) {
					case LEFT  : return right(x->sp1);
					case RIGHT : return right(x->sp2);
					default    : return NULL;
				}
			}
			if (eqr(right(x->sp1),left(x->sp2))) {
				switch(s) {
					case LEFT  : return left(x->sp1);
					case RIGHT : return right(x->sp2);
					default    : return NULL;
				}
			}
			if (eqr(left(x->sp1),right(x->sp2))) {
				switch(s) {
					case LEFT  : return right(x->sp1);
					case RIGHT : return left(x->sp2);
					default    : return NULL;
				}
			}
			if (eqr(right(x->sp1),right(x->sp2))) {
				switch(s) {
					case LEFT  : return left(x->sp1);
					case RIGHT : return left(x->sp2);
					default    : return NULL;
				}
			}
			return x;
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
		case RFE :
			//return x->sp1;
			return equ(left(x->sp1),right(x->sp1));
		default :
			y = mkproof(x->op, side(s,x->sp1), side(s,x->sp2));
			// y->cert = cert(x->sp1) * cert(x->sp2);
			return y;
	}
}

proof side (int s, proof x) {
	int i;
	if (x == NULL)
		return x;
	for (i=LEFT; i==LEFT||i==RIGHT; i+=RIGHT-LEFT) {
		if (x->side[i] == NULL)
			x->side[i] = side1(i,x);
	}
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
	//printf ("\ncertainty of ");
	//print_proof_to_stdout(x);
	if (x == NULL) return 1.0;
	if (x->cert == NOCERT)
		// x->cert = cert(x->sp1) * cert(x->sp2);
		return cert(x->sp1) * cert(x->sp2);
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
		if (cur_char == 0 || cur_char == -1 || strchr(" \t\n\r()[]#=;.",cur_char)) break;
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
		case '-' :
			nextchar(reader);
			x = read_proof_1(reader);
			y = read_proof_1(reader);
			return apl(x,y);
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
			nextchar(reader);
			skip_blanks(reader);
			read_name(reader,name);
			x = read_proof_1(reader);
			for (i=0; i<nproofs; i++) {
				if (!strcmp(proofs[i].name,name)) {
					printf("\nAnother proof has the name \"%s\".\n", name);
					return x;
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

proof read_proof_2 (struct reader *reader, int options) {
	proof x, y, z, t;
	x = NULL;
	y = NULL;
	t = NULL;
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
				if (t == NULL) {
					if (x == NULL) {
						if ((y == NULL) && (options & 1)) return empty_proof;
						return y;
					}
					return equ(x,y);
				} else {
					if (x == NULL) return gtr(t,y);
					return gtr(t,equ(x,y));
				}
			case '=' :
				nextchar(reader);
				if (x == NULL) {
					x = y;
				} else {
					x = equ(x,y);
				}
				y = NULL;
				break;
			case ';' :
				nextchar(reader);
				if (t == NULL) {
					if (x == NULL) {
						t = y;
					} else {
						t = equ(x,y);
					}
				} else {
					if (x == NULL) {
						t = gtr(t,y);
					} else {
						t = gtr(t,equ(x,y));
					}
				}
				x = NULL;
				y = NULL;
				break;
			case ':' :
				nextchar(reader);
				z = read_proof_2(reader, 1);
				if (y == NULL) y = z;
				else y = apl(y,z);
				break;
			default :
				z = read_proof_1(reader);
				if (y == NULL) y = z;
				else y = apl(y,z);
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
	if (x == NULL) {
		putstring_to_printer(printer, "0");
		return;
	}
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
	switch(x->op) {
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
			putstring_to_printer(printer, "_");
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
		case GTR : 
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
		default :
			sprintf(buf,"%c", x->op);
			putstring_to_printer(printer, buf);
			for (i=0; i<N_OPERATORS; i++) {
				if (operators[i].code == x->op) {
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
	if (x->cert != NOCERT && x->cert != 1.0) {
		putstring_to_printer(printer, ")");
	}
	if (x->val != NULL) {
		proof v;
		v = x->val;
		x->val = NULL;
		putstring_to_printer(printer, "{");
		print_proof_1(printer,v,0,full);
		putstring_to_printer(printer, "}");
		x->val = v;
	}
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

int main (int argc, char *argv[]) {
	char buf[100000];
	proof x, y, l, r;
	FILE *f;
	char *filename;
	int quiet;
	int print_red;
	struct reader reader;
	
	init();
	empty_proof = fnc(var);
	filename = NULL;
	quiet = 0;
	print_red = 0;
	quiet_read = 0;
	
	if (argc > 1) {
		if (argv[1][0] == '-') {
			if (argc > 2) filename = argv[2];
			if (strchr(argv[1],'q')) quiet = 1;
			if (strchr(argv[1],'Q')) quiet_read = 1;
			if (strchr(argv[1],'r')) print_red = 1;
		} else {
			filename = argv[1];
		}
	}
	
	if (filename) {
		f = fopen(filename, "r");
		if (f == NULL) {
			printf("\nCannot open file %s.\n", filename);
			exit(1);
		}
		read_from_file(&reader, f);
		for (;;) {
			// x = read_proof_from_file_2(f);
			nextchar(&reader);
			x = read_proof_2(&reader, 0);
			if (x == NULL) break;
			y = reduce(x);
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
		}
		printf("\n");
		fclose(f);
		return 0;
	}

	printf("Welcome to Proof Logic !\n");
	printf("Type a proof ended by \".\", and type just \".\" to quit.\n");
	read_from_stdin(&reader);

	for (;;) {
		printf("\n? ");
		// x = read_proof_from_stdin();
		nextchar(&reader);
		x = read_proof_2(&reader, 0);
		if (x == NULL) break;
		y = reduce(x);
		l = left(x);
		r = right(x);
		printf("\nThe proof  : ");
		print_proof_to_stdout(x);
		printf ("\nreduces to : ");
		print_proof_to_stdout(y);
		printf ("\nand proves : ");
		print_proof_to_stdout(l);
		printf ("\nequals     : ");
		print_proof_to_stdout(r);
		if (cert(x) != NOCERT && cert(x) != 1.0) {
			printf ("\ncertainty  : ");
			printf("%5.3f",cert(x));
		}
		printf("\n");
	}
}

