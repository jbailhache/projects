/* Proof Logic by Jacques Bailhache (jacques.bailhache@gmail.com) */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>


struct reader {
	char (*getchar)(struct reader *);
	void *p;
};

char getchar_from_reader (struct reader *reader) {
	char c;
	c = (*(reader->getchar))(reader);
	//printf(" '%c'[%02X] ", c, c);
	//if (c == 0) c = '.';
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
	return fgetc((FILE *)(reader->p));
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


#define LEFT  0
#define RIGHT 1

#define SMB '_'
#define VAR '*'
#define NXV '\''
#define FNC '['
#define RED '@'
#define RLR '$'
#define APL '-'
#define LTR '{'
#define RTR '<'
#define EQU '='
#define RSL '/'
#define RSR '\\'
#define PRT '?'

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
	{ PRT, 2 }
};	

#define N_OPERATORS (sizeof(operators)/sizeof(operators[0]))

typedef struct proof1 *proof;

struct proof1 {
	int op;
	char name[16];
	proof sp1, sp2, red, side[2];	
};

#define MAXPROOFS 100000

int nproofs;

struct proof1 proofs[MAXPROOFS];

void print_proof_to_stdout (proof x);

void init() {
	nproofs = 0;
	proofs[nproofs].op = VAR;
	proofs[nproofs].red = proofs+nproofs;
	proofs[nproofs].side[LEFT] = proofs+nproofs;
	proofs[nproofs].side[RIGHT] = proofs+nproofs;
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
	strcpy(proofs[nproofs].name,name);
	return proofs+nproofs++;
}

#define DEFOP1(o,f) \
proof f(proof x) { \
	int i; \
	for (i=0; i<nproofs; i++) { \
		if (proofs[i].op == o && proofs[i].sp1 == x) \
			return proofs+i; \
	} \
	check_memory(); \
	proofs[nproofs].op = o; \
	proofs[nproofs].sp1 = x; \
	return proofs+nproofs++; \
}

DEFOP1(NXV,nxv)
DEFOP1(FNC,fnc)
DEFOP1(RED,red)
DEFOP1(RLR,rlr)
DEFOP1(RSL,rsl)
DEFOP1(RSR,rsr)

#define DEFOP2(o,f) \
proof f(proof x, proof y) { \
	int i; \
	for (i=0; i<nproofs; i++) { \
		if (proofs[i].op == o && proofs[i].sp1 == x && proofs[i].sp2 == y) \
			return proofs+i; \
	} \
	check_memory(); \
	proofs[nproofs].op = o; \
	proofs[nproofs].sp1 = x; \
	proofs[nproofs].sp2 = y; \
	return proofs+nproofs++; \
}

DEFOP2(APL,apl)
DEFOP2(LTR,ltr)
DEFOP2(RTR,rtr)
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
	return proofs+nproofs++; 
}

// shift(u,x) increases all variables greater than u in x
proof shift (proof u, proof x) {
	if (x == u) return nxv(x);
	if (x == NULL) return x;
	switch (x->op) {
		case SMB :
			return x;
		case VAR :
			//if (u->op == VAR) return nxv(var);
			return x;
		//case NXV :
			//if (u->op == NXV) return nxv(shift(u->sp1,x->sp1));
			//return nxv(shift(u,x->sp1));
		case FNC :
			return fnc(shift(nxv(u),x->sp1));
		default :
			return mkproof(x->op,shift(u,x->sp1),shift(u,x->sp2));
	}
}

/*
proof shift (proof u, proof x) {
	//if (x == u) return nxv(x);
	if (x == NULL) return x;
	switch (x->op) {
		case SMB :
			return x;
		case VAR :
			if (u->op == VAR) return nxv(var);
			return x;
		case NXV :
			if (u->op == NXV) return nxv(shift(u->sp1,x->sp1));
			return nxv(shift(u,x->sp1));
		case FNC :
			return fnc(shift(nxv(u),x->sp1));
		default :
			return mkproof(x->op,shift(u,x->sp1),shift(u,x->sp2));
	}
}
*/

proof subst (proof u, proof a, proof b) {
	if (u == a) return b;
	//if (u->op == NXV && u->sp1 == a) return u;
	if (a == NULL) return a;
	if (a->op == NXV && a->sp1 == u) return u;
	switch (a->op) {
		case SMB :
		case VAR :
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
	if (x->op == APL && x->sp1->op == FNC)
		return subst(var, x->sp1->sp1, x->sp2);
	//if (x->op == RED) 
	//	return reduce1(x->sp1);
	/*if (x->op == PRT) {
		l = left(x->sp2);
		r = right(x->sp2);
		printf("\nreduce1 : \nThe proof : ");
		print_proof_to_stdout(x->sp1);
		printf("\nproves    : ");
		print_proof_to_stdout(l);
		printf("\nequals    : ");
		print_proof_to_stdout(r);
		printf("\n");		
		return x->sp2;
	}*/
	return mkproof(x->op, reduce1(x->sp1), reduce1(x->sp2));
}
			
/*
proof reduce (proof x) {
	proof y;
	if (x == NULL) return x;
	if (x->red != NULL)
		return x->red;
	y = reduce1(x);
	if (y == x) 
		x->red = y;
	else
		x->red = reduce(y);
	return x->red;
}
*/


/*
proof reduce2 (proof x) {
	proof y;
	if (x == NULL) return x;
	y = reduce1(x);
	if (y == x)
		return y;
	else
		return reduce2(y);
}
*/

/*
proof reduce2 (proof x) {
	proof y, z;
	if (x == NULL) return x;
	y = x;
	for (;;)
	{
		z = reduce1(y);
		if (z == y) break;
		y = z;
	}
	return z;
}
*/

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
		//printf("reduce2: ");
		//print_proof_to_stdout(y);
		//printf("\n");
		a[n++] = y;
		z = reduce1(y);
		//if (z == y) break;
		if (n >= MAX) break;
		found = 0;
		for (i=0; i<n; i++) {
			if (contsp(z,a[i])) {
				found = 1;
				break;
			} 
		}
		//if (found) break;
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


int eqr (proof x, proof y) {
	return 
		x == y ||
		x == reduce(y) ||
		reduce(x) == y ||
		reduce(x) == reduce(y);
}

proof side (int s, proof x);
proof left (proof x);
proof right (proof x);

proof side1 (int s, proof x) {
	proof y, z;
	if (x == NULL) return NULL;
	switch (x->op) {
		case SMB :
			return x;
		case EQU : 
			switch(s) {
				case LEFT  :  return x->sp1;
				case RIGHT : return x->sp2;
				default    : return NULL;
			}
		//case APL :
		//	return reduce(apl(side(s,x->sp1),side(s,x->sp2)));
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
		case LTR :
			//if (reduce(side(1,x->sp1)) == reduce(side(1,x->sp2)))
			// y = reduce(side(LEFT,x->sp1));
			// z = reduce(side(LEFT,x->sp2));
			// if (y == z || y == side(LEFT,x->sp2) || side(LEFT,x->sp1) == z)
			if (eqr(left(x->sp1),left(x->sp2))) {
				// return right(s==LEFT ? x->sp1 : x->sp2);
				switch(s) {
					case LEFT  : return right(x->sp1);
					case RIGHT : return right(x->sp2);
					default    : return NULL;
				}
			}
			if (eqr(right(x->sp1),right(x->sp2))) {
				// return left(s==LEFT ? x->sp1 : x->sp2);
				switch(s) {
					case LEFT  : return left(x->sp1);
					case RIGHT : return left(x->sp2);
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
			printf("LTR does not apply to ");
			print_proof_to_stdout(x);
			printf("\n first  proof reduces to ");
			print_proof_to_stdout(y);
			printf("\n second proof reduces to ");
			print_proof_to_stdout(z);
			printf("\n");
			return x;
		case RTR :
			//if (reduce(side(0,x->sp1)) == reduce(side(0,x->sp2)))
			// y = reduce(side(RIGHT,x->sp1));
			// z = reduce(side(RIGHT,x->sp2));
			// if (y == z || y == side(RIGHT,x->sp2) || side(RIGHT,x->sp1) == z)
			if (eqr(right(x->sp1),right(x->sp2))) 
				return left(s==LEFT ? x->sp1 : x->sp2);
			printf("RTR does not apply to ");
			print_proof_to_stdout(x);
			printf("\n first  proof reduces to ");
			print_proof_to_stdout(y);
			printf("\n second proof reduces to ");
			print_proof_to_stdout(z);
			printf("\n");			
			return x;
		case PRT :
			y=side(s,x->sp2);
			//y = reduce(side(s,x->sp2));
			switch(s) {
				case LEFT  : printf("\nLeft  of ");
				case RIGHT : printf("Right of ");
				default    : ;
			}
			print_proof_to_stdout(x->sp1);
			printf(" is : ");
			print_proof_to_stdout(y);
			printf("\n");
			return y;
		default :
			return mkproof(x->op, side(s,x->sp1), side(s,x->sp2));
	}
}

proof side (int s, proof x) {
	int i;
	if (x == NULL)
		return x;
	//if (x->side[s] == NULL)
	//	x->side[s] = side1(s,x);
	//for (i=1; i>=0; i--) {
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

proof abstr (proof u, proof v, proof x) {
	if (v == x) return u;
	if (!cont(x,v)) return x;
	if (x == NULL) return x;
	if (x->op == FNC) 
		return fnc(abstr(nxv(u),v,x->sp1));
	return mkproof(x->op, abstr(u,v,x->sp1), abstr(u,v,x->sp2));
}

proof lambda (proof v, proof x) {
	return fnc(abstr(var,v,x));
}

proof simple_read_proof_1 (struct reader *reader) {
	char c;
	proof x, y;
	char name[4];
	c = getchar_from_reader(reader);
	switch(c) {
		case ' ' :
			return simple_read_proof_1(reader);
		case '*' : 
			return var;
		case '\'' :
			x = simple_read_proof_1(reader);
			return nxv(x);
		case '\\':
			x = simple_read_proof_1(reader);
			return fnc(x);
		case '@' :
			x = simple_read_proof_1(reader);
			return red(x);
		case '-' :
			x = simple_read_proof_1(reader);
			y = simple_read_proof_1(reader);
			return apl(x,y);
		case '/' : 
			x = simple_read_proof_1(reader);
			y = simple_read_proof_1(reader);
			return ltr(x,y);
		case '%' :
			x = simple_read_proof_1(reader);
			y = simple_read_proof_1(reader);
			return rtr(x,y);
		case '#' :
			x = simple_read_proof_1(reader);
			y = simple_read_proof_1(reader);
			return equ(x,y);
		default :
			name[0] = c;
			name[1] = 0;
			return smb(name);
	}
}

proof simple_read_proof (char *s) {
	struct reader reader;
	read_from_string(&reader,s);
	return simple_read_proof_1(&reader);
}

void simple_print_proof_1(struct printer *printer, proof x) {
	switch(x->op) {
		case SMB :
			putstring_to_printer (printer, x->name);
			break;
		case VAR :
			putchar_to_printer (printer, '*');
			break;
		case NXV :
			putchar_to_printer (printer, '\'');
			simple_print_proof_1 (printer, x->sp1);
			break;
		case FNC :
			putchar_to_printer (printer, '\\');
			simple_print_proof_1 (printer, x->sp1);
			break;
		case RED :
			putchar_to_printer (printer, '@');
			simple_print_proof_1 (printer, x->sp1);
			break;
		case APL :
			putchar_to_printer (printer, '-');
			simple_print_proof_1 (printer, x->sp1);
			simple_print_proof_1 (printer, x->sp2);
			break;
		case LTR :
			putchar_to_printer (printer, '/');
			simple_print_proof_1 (printer, x->sp1);
			simple_print_proof_1 (printer, x->sp2);
			break;
		case RTR :
			putchar_to_printer (printer, '%');
			simple_print_proof_1 (printer, x->sp1);
			simple_print_proof_1 (printer, x->sp2);
			break;
		case EQU :
			putchar_to_printer (printer, '#');
			simple_print_proof_1 (printer, x->sp1);
			simple_print_proof_1 (printer, x->sp2);
			break;
	}
}

void simple_print_proof (proof x) {
	struct printer printer;
	print_to_stdout(&printer);
	simple_print_proof_1(&printer,x);
}

int cur_char;

int nextchar (struct reader *reader) {
	cur_char = getchar_from_reader(reader);
	if (cur_char == '#') {
		while (cur_char != '\n' && cur_char != -1) {
			cur_char = getchar_from_reader(reader);
		}
		//cur_char = getchar_from_reader(reader);
	}
	//printf("%c",cur_char);
	return cur_char;
}

void skip_blanks(struct reader *reader) {
	while (cur_char != 0 && strchr(" \t\n\r",cur_char)) 
		nextchar(reader);
	//if (cur_char == '#') {
	//	while (cur_char != '\n') {
	//		nextchar(reader);
	//	}
	//}
}

proof read_proof_2 (struct reader *reader);

proof read_proof_1 (struct reader *reader) {
	char c;
	proof x, y, z, l, r, a[2];
	char name[32];
	int i, j;
	skip_blanks(reader);
	switch(cur_char) {
		case 0 :
		case -1 :
			return smb("NULL");
		case '*' :
			nextchar(reader);
			return var;
		/*
		case '\'' :
			nextchar(reader);
			x = read_proof_1(reader);
			return nxv(x);
		case '@' :
			nextchar(reader);
			x = read_proof_1(reader);
			return red(x);
		case '/' :
		//case '$' :
			nextchar(reader);
			x = read_proof_1(reader);
			return rsl(x);
		case '\\' :
		//case '&' :
			nextchar(reader);
			x = read_proof_1(reader);
			return rsr(x);
		case '?' :
			nextchar(reader);
			x = read_proof_1(reader);
			y = read_proof_1(reader);
			return prt(x,y);
		*/
		case '-' :
			nextchar(reader);
			x = read_proof_1(reader);
			y = read_proof_1(reader);
			return apl(x,y);
		case '(' :
			nextchar(reader);
			x = read_proof_2(reader);
			if (cur_char == ')')
				nextchar(reader);
			return x;
		case '[' :
			nextchar(reader);
			x = read_proof_2(reader);
			if (cur_char == ']')
				nextchar(reader);
			return fnc(x);
		case '{' : 
			nextchar(reader);
			x = read_proof_2(reader);
			if (cur_char == ',')
				nextchar(reader);
			y = read_proof_2(reader);
			if (cur_char == '}')
				nextchar(reader);
			return ltr(x,y);
		case '<' : 
			nextchar(reader);
			x = read_proof_2(reader);
			if (cur_char == ',' || cur_char == '|')
				nextchar(reader);
			y = read_proof_2(reader);
			if (cur_char == '>')
				nextchar(reader);
			return rtr(x,y);
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
			/*
			l = left(y);
			r = right(y);
			printf("\nRead proof");
			printf("\nThe proof : ");
			print_proof_to_stdout(x);
			printf("\nproves    : ");
			print_proof_to_stdout(l);
			printf("\nequals     : ");
			print_proof_to_stdout(r);
			printf("\n");
			*/
			z = read_proof_1(reader);
			//return red(apl(lambda(x,z),y));
			return red(apl(lambda(x,z),prt(x,y)));
		default :
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
			i = 0;
			for (;;) {
				if (!cur_char) break;
				if (cur_char == 0 || cur_char == -1 || strchr(" \t\n\r()*'\\[]-/%{,}<|>#=.",cur_char)) break;
				if (i>=sizeof(name)-1) break;
				name[i++] = cur_char;
				nextchar(reader);
			}
			name[i] = 0;
			return smb(name);			
	}
}

proof read_proof_2 (struct reader *reader) {
	proof x, y, z;
	x = NULL;
	y = NULL;
	for (;;) {
		skip_blanks(reader);
		switch(cur_char) {
			case 0 :
			case -1 :
			case ')' :
			case ']' :
			case ',' :
			case '}' :
			case '|' :
			case '>' :
			case '.' :
				if (x == NULL) return y;
				return equ(x,y);
			case '=' :
				nextchar(reader);
				if (x == NULL) {
					x = y;
				} else {
					x = equ(x,y);
				}
				y = NULL;
				break;
			case ':' :
				nextchar(reader);
				z = read_proof_2(reader);
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
	//char buf[100000];
	//sprintf(buf,"%s.",s);
	//read_from_string(&reader,buf);
	read_from_string(&reader,s);
	//cur_char = getchar_from_reader(&reader);
	nextchar(&reader);
	return read_proof_2(&reader);
}

proof read_proof_from_stdin () {
	struct reader reader;
	read_from_stdin(&reader);
	nextchar(&reader);
	return read_proof_2(&reader);
}

proof read_proof_from_file (FILE *f) {
	struct reader reader;
	read_from_file(&reader, f);
	nextchar(&reader);
	return read_proof_1(&reader);
}

void print_proof_1(struct printer *printer, proof x, int parenthesized) {
	char buf[100];
	int i, j;
	if (x == NULL) {
		putstring_to_printer(printer, "0");
		return;
	}
	/*if (x == read_proof_from_string("[* *] [[imp * false] (* *)].")) {
		putstring_to_printer(printer,"contrad");
		return;
	}*/
	switch(x->op) {
		case SMB :
			putstring_to_printer(printer, x->name);
			break;
		case VAR :
			putstring_to_printer(printer, "*");
			break;
		/*
		case NXV :
			putstring_to_printer(printer, "'");
			print_proof_1(printer, x->sp1, 1);
			break;
		*/
		case FNC :
			putstring_to_printer(printer, "[");
			print_proof_1(printer, x->sp1, 0);
			putstring_to_printer(printer, "]");
			break;
		/*
		case RED :
			putstring_to_printer(printer, "@");
			print_proof_1(printer, x->sp1, 1);
			break;
		case RSL :
			//putstring_to_printer(printer, "$");
			putstring_to_printer(printer, "/");
			print_proof_1(printer, x->sp1, 1);
			break;
		case RSR :
			//putstring_to_printer(printer, "&");
			putstring_to_printer(printer, "\\");
			print_proof_1(printer, x->sp1, 1);
			break;
		case PRT :
			putstring_to_printer(printer, "?");
			print_proof_1(printer, x->sp1, 1);
			putstring_to_printer(printer," ");
			print_proof_1(printer, x->sp2, 1);
			break;
		*/
		case APL :
			if (parenthesized & 2) putstring_to_printer(printer, "(");
			print_proof_1(printer, x->sp1, 1);
			putstring_to_printer(printer, " ");
			print_proof_1(printer, x->sp2, 3);
			if (parenthesized & 2) putstring_to_printer(printer, ")");
			break;
		case LTR : 
			putstring_to_printer(printer, "{ ");
			print_proof_1(printer, x->sp1, 0);
			putstring_to_printer(printer, " , ");
			print_proof_1(printer, x->sp2, 0);
			putstring_to_printer(printer, " }");
			break;
		case RTR : 
			putstring_to_printer(printer, "< ");
			print_proof_1(printer, x->sp1, 0);
			//putstring_to_printer(printer, " | ");
			putstring_to_printer(printer, " , ");
			print_proof_1(printer, x->sp2, 0);
			putstring_to_printer(printer, " >");
			break;
		case EQU :
			if (parenthesized & 1) putstring_to_printer(printer, "(");
			print_proof_1(printer, x->sp1, 0);
			putstring_to_printer(printer, " = ");
			print_proof_1(printer, x->sp2, 0);
			if (parenthesized & 1) putstring_to_printer(printer, ")");
			break;
		default :
			sprintf(buf,"%c", x->op);
			putstring_to_printer(printer, buf);
			for (i=0; i<N_OPERATORS; i++) {
				if (operators[i].code == x->op) {
					if (operators[i].arity > 0) {
						print_proof_1(printer, x->sp1, 3);
						if (operators[i].arity > 1) {
							putstring_to_printer(printer, " ");
							print_proof_1(printer, x->sp2, 3);
						}
					}
				}
			}					
	}
}
		
void print_proof_to_stdout (proof x) {
	struct printer printer;
	print_to_stdout(&printer);
	print_proof_1(&printer,x,0);
}


void dump () {
	/*
	int i;
	for (i=0; i<nproofs; i++) {
		printf("%8lx %c %-8s %8lx %8lx\n", 
			(unsigned long)(proofs+i), 
			proofs[i].op, 
			proofs[i].name, 
			(unsigned long)(proofs[i].sp1), 
			(unsigned long)(proofs[i].sp2));
	}
	*/
}

int test() {
	/*
	char buf[1000];
	proof x;
	init();
	for (;;) {
		dump();
		printf("? ");
		fgets(buf,sizeof(buf),stdin);
		x = read_proof_from_string(buf);
		printf("%8lx ",(unsigned long)x);
		simple_print_proof(x);
		printf(" ");
		print_proof_to_stdout(x);
		printf("\n\n");
	}
	*/
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

int main (int argc, char *argv[]) {
	char buf[100000];
	proof x, y, l, r;
	FILE *f;
	init();
	/*
	x = red(apl(lambda(smb("I"),apl(smb("I"),smb("a"))),fnc(var)));
	print_proof_to_stdout(x);
	printf(" reduces to ");
	print_proof_to_stdout(reduce(x));
	printf("\n");
	*/
	if (argc > 1) {
		//read_file(argv[1], buf);
		//strcat(buf,".");
		//x = read_proof_from_string(buf);
		f = fopen(argv[1], "r");
		x = read_proof_from_file(f);
		l = left(x);
		r = right(x);
		printf("\nThe proof : ");
		print_proof_to_stdout(x);
		printf("\nproves    : ");
		print_proof_to_stdout(l);
		printf("\nequals    : ");
		print_proof_to_stdout(r);
		printf("\n");
		fclose(f);
		return 0;
	}
	printf("Welcome to Proof Logic !\n");
	printf("Type a proof ended by \".\", and type just \".\" to quit.\n");
	for (;;) {
		printf("\n? ");
		//fgets(buf, sizeof(buf), stdin);
		//strcat(buf,".");
		//x = read_proof_from_string(buf);
		x = read_proof_from_stdin();
		if (x == NULL) break;
		y = reduce(x);
		l = left(x);
		r = right(x);
		printf("\nThe proof  : ");
		print_proof_to_stdout(x);
		printf ("\nreduces to : ");
		print_proof_to_stdout(y);
		printf ("\nand proves : ");
		//printf("\nproves\n");
		print_proof_to_stdout(l);
		printf ("\nequals     : ");
		print_proof_to_stdout(r);
		printf("\n");
	}
}

