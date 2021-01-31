
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
	// printf(" %c[%02X] ", c, c);
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


#define SMB '$'
#define VAR '*'
#define NXV '\''
#define FNC '\\'
#define RED '@'
#define APL '-'
#define LTR '/'
#define RTR '%'
#define EQU '='

typedef struct proof *proof;

struct proof {
	int op;
	char name[8];
	proof sp1, sp2, red, side[2];	
};

#define MAXPROOFS 1000

int nproofs;

struct proof proofs[MAXPROOFS];

void init() {
	nproofs = 0;
	proofs[nproofs].op = VAR;
	proofs[nproofs].red = proofs+nproofs;
	proofs[nproofs].side[0] = proofs+nproofs;
	proofs[nproofs].side[1] = proofs+nproofs;
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
	proofs[nproofs].side[0] = NULL;
	proofs[nproofs].side[1] = NULL;
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

proof shift (proof u, proof x) {
	if (x == u) return nxv(x);
	if (x == NULL) return x;
	switch (x->op) {
		case SMB :
		case VAR :
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

proof subst (proof u, proof a, proof b) {
	if (u == a) return b;
	if (u->op == NXV && u->sp1 == a) return u;
	if (a == NULL) return a;
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

proof reduce1 (proof x) {
	if (x == NULL) return x;
	if (x->op == SMB) return x;
	if (x->op == APL && x->sp1->op == FNC)
		return subst(var, x->sp1->sp1, x->sp2);
	return mkproof(x->op, reduce1(x->sp1), reduce1(x->sp2));
}
			
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

proof side (int s, proof x);

proof side1 (int s, proof x) {
	if (x == NULL) return NULL;
	switch (x->op) {
		case SMB :
			return x;
		case EQU : 
			if (s) 
				return x->sp1;
			else
				return x->sp2;
		case RED :
			return side(s,reduce(x));
		case LTR :
			if (reduce(side(1,x->sp1)) == reduce(side(1,x->sp2)))
				return side(0, s ? x->sp1 : x->sp2);
			return x;
		case RTR :
			if (reduce(side(0,x->sp1)) == reduce(side(0,x->sp2)))
				return side(1, s ? x->sp1 : x->sp2);
			return x;
		default :
			return mkproof(x->op, side(s,x->sp1), side(s,x->sp2));
	}
}

proof side (int s, proof x) {
	if (x == NULL)
		return x;
	if (x->side[s] == NULL)
		x->side[s] = side1(s,x);
	return x->side[s];
}
	
proof left (proof x) {
	return side(1,x);
}

proof right (proof x) {
	return side(0,x);
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

char cur_char;

void skip_blanks(struct reader *reader) {
	while (strchr(" \t\n\r",cur_char)) cur_char = getchar_from_reader(reader);
}

proof read_proof_2 (struct reader *reader);

proof read_proof_1 (struct reader *reader) {
	char c;
	proof x, y;
	char name[16];
	int i;
	skip_blanks(reader);
	switch(cur_char) {
		case 0 :
			return smb("ZERO");
		case '*' :
			cur_char = getchar_from_reader(reader);
			return var;
		case '\'' :
			cur_char = getchar_from_reader(reader);
			x = read_proof_1(reader);
			return nxv(x);
		case '\\' :
			cur_char = getchar_from_reader(reader);
			x = read_proof_1(reader);
			return fnc(x);
		case '@' :
			cur_char = getchar_from_reader(reader);
			x = read_proof_1(reader);
			return red(x);
		case '-' :
			cur_char = getchar_from_reader(reader);
			x = read_proof_1(reader);
			y = read_proof_1(reader);
			return apl(x,y);
		case '/' :
			cur_char = getchar_from_reader(reader);
			x = read_proof_1(reader);
			y = read_proof_1(reader);
			return ltr(x,y);
		case '%' :
			cur_char = getchar_from_reader(reader);
			x = read_proof_1(reader);
			y = read_proof_1(reader);
			return rtr(x,y);
		case '#' :
			cur_char = getchar_from_reader(reader);
			x = read_proof_1(reader);
			y = read_proof_1(reader);
			return equ(x,y);
		case '(' :
			cur_char = getchar_from_reader(reader);
			x = read_proof_2(reader);
			if (cur_char == ')')
				cur_char = getchar_from_reader(reader);
			return x;
		case '[' :
			cur_char = getchar_from_reader(reader);
			x = read_proof_2(reader);
			if (cur_char == ']')
				cur_char = getchar_from_reader(reader);
			return fnc(x);
		case '{' : 
			cur_char = getchar_from_reader(reader);
			x = read_proof_2(reader);
			if (cur_char == ',')
				cur_char = getchar_from_reader(reader);
			y = read_proof_2(reader);
			if (cur_char == '}')
				cur_char = getchar_from_reader(reader);
			return ltr(x,y);
		case '<' : 
			cur_char = getchar_from_reader(reader);
			x = read_proof_2(reader);
			if (cur_char == '|')
				cur_char = getchar_from_reader(reader);
			y = read_proof_2(reader);
			if (cur_char == '>')
				cur_char = getchar_from_reader(reader);
			return rtr(x,y);
		default :
			i = 0;
			for (;;) {
				if (!cur_char) break;
				if (cur_char == 0 || strchr(" \t\n\r()*'\\[]-/%{,}<|>#=.",cur_char)) break;
				if (i>=sizeof(name)-1) break;
				name[i++] = cur_char;
				cur_char = getchar_from_reader(reader);
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
				cur_char = getchar_from_reader(reader);
				if (x == NULL) {
					x = y;
				} else {
					x = equ(x,y);
				}
				y = NULL;
				break;
			case ':' :
				cur_char = getchar_from_reader(reader);
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

proof read_proof (char *s) {
	struct reader reader;
	char buf[1000];
	sprintf(buf,"%s.",s);
	read_from_string(&reader,buf);
	cur_char = getchar_from_reader(&reader);
	return read_proof_2(&reader);
}

void print_proof_1(struct printer *printer, proof x, int parenthesized) {
	char buf[100];
	switch(x->op) {
		case SMB :
			putstring_to_printer(printer, x->name);
			break;
		case VAR :
			putstring_to_printer(printer, "*");
			break;
		case NXV :
			putstring_to_printer(printer, "'");
			print_proof_1(printer, x->sp1, 1);
			break;
		case FNC :
			putstring_to_printer(printer, "[");
			print_proof_1(printer, x->sp1, 0);
			putstring_to_printer(printer, "]");
			break;
		case RED :
			putstring_to_printer(printer, "@");
			print_proof_1(printer, x->sp1, 1);
			break;
		case APL :
			if (parenthesized) putstring_to_printer(printer, "(");
			print_proof_1(printer, x->sp1, 0);
			putstring_to_printer(printer, " ");
			print_proof_1(printer, x->sp2, 1);
			if (parenthesized) putstring_to_printer(printer, ")");
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
			putstring_to_printer(printer, " | ");
			print_proof_1(printer, x->sp2, 0);
			putstring_to_printer(printer, " >");
			break;
		case EQU :
			putstring_to_printer(printer, "( ");
			print_proof_1(printer, x->sp1, 0);
			putstring_to_printer(printer, " = ");
			print_proof_1(printer, x->sp2, 0);
			putstring_to_printer(printer, " )");
			break;
		default :
			sprintf(buf,"%x", x->op);
			putstring_to_printer(printer, buf);
	}
}
		
void print_proof (proof x) {
	struct printer printer;
	print_to_stdout(&printer);
	print_proof_1(&printer,x,0);
}


void dump () {
	int i;
	for (i=0; i<nproofs; i++) {
		printf("%8x %c %-8s %8x %8x\n", proofs+i, proofs[i].op, proofs[i].name, proofs[i].sp1, proofs[i].sp2);
	}
}

int test() {
	char buf[1000];
	proof x;
	init();
	for (;;) {
		dump();
		printf("? ");
		fgets(buf,sizeof(buf),stdin);
		x = read_proof(buf);
		printf("%8x ",x);
		simple_print_proof(x);
		printf(" ");
		print_proof(x);
		printf("\n\n");
	}
}

int main() {
	char buf[1000];
	proof x;
	init();
	for (;;) {
		printf("? ");
		fgets(buf, sizeof(buf), stdin);
		x = read_proof(buf);
		print_proof(x);
		printf (" proves ");
		print_proof(left(x));
		printf (" equals ");
		print_proof(right(x));
		printf("\n");
	}
}
