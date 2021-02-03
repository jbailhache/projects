
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
	fputc(c, printer->p);
}

void print_to_file (struct printer *printer, FILE *f) {
	printer->putchar = putchar_to_file;
	printer->p = f;
}

#define SMB '_'
#define VAR '*'
#define NXV '\''
#define FNC '\\'
#define RED '@'
#define APL '-'
#define LTR '/'
#define RTR '%'
#define EQU '='
#define RSL '$'
#define RSR '&'

typedef struct proof *proof;

struct proof {
	int op;
	char name[16];
	proof sp1, sp2, red, side[2];	
};

#define MAXPROOFS 100000

int nproofs;

struct proof proofs[MAXPROOFS];

void print_proof_to_stdout (proof x);

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


proof reduce (proof x);

proof reduce1 (proof x) {
	if (x == NULL) return x;
	if (x->op == SMB) return x;
	if (x->op == APL && x->sp1->op == FNC)
		return subst(var, x->sp1->sp1, x->sp2);
	//if (x->op == RED) 
	//	return reduce1(x->sp1);
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


proof side (int s, proof x);

proof side1 (int s, proof x) {
	proof y, z;
	if (x == NULL) return NULL;
	switch (x->op) {
		case SMB :
			return x;
		case EQU : 
			if (s) 
				return x->sp1;
			else
				return x->sp2;
		//case APL :
		//	return reduce(apl(side(s,x->sp1),side(s,x->sp2)));
		case RED :
			return side(s,reduce(x->sp1));
		case RSL :
			if (s) return reduce1(side(s,x->sp1));
			else   return side(s,x->sp1);
		case RSR :
			if (s) return side(s,x->sp1);
			else   return reduce1(side(s,x->sp1));
		case LTR :
			//if (reduce(side(1,x->sp1)) == reduce(side(1,x->sp2)))
			y = reduce(side(1,x->sp1));
			z = reduce(side(1,x->sp2));
			if (y == z || y == side(1,x->sp2) || side(1,x->sp1) == z)
				return side(0, s ? x->sp1 : x->sp2);
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
			y = reduce(side(0,x->sp1));
			z = reduce(side(0,x->sp2));
			if (y == z || y == side(0,x->sp2) || side(0,x->sp1) == z)
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
	proof x, y, z;
	char name[32];
	int i;
	skip_blanks(reader);
	switch(cur_char) {
		case 0 :
		case -1 :
			return smb("NULL");
		case '*' :
			nextchar(reader);
			return var;
		case '\'' :
			nextchar(reader);
			x = read_proof_1(reader);
			return nxv(x);
		case '\\' :
			nextchar(reader);
			x = read_proof_1(reader);
			return fnc(x);
		case '@' :
			nextchar(reader);
			x = read_proof_1(reader);
			return red(x);
		case '$' :
			nextchar(reader);
			x = read_proof_1(reader);
			return rsl(x);
		case '&' :
			nextchar(reader);
			x = read_proof_1(reader);
			return rsr(x);
		case '-' :
			nextchar(reader);
			x = read_proof_1(reader);
			y = read_proof_1(reader);
			return apl(x,y);
		case '/' :
			nextchar(reader);
			x = read_proof_1(reader);
			y = read_proof_1(reader);
			return ltr(x,y);
		case '%' :
			nextchar(reader);
			x = read_proof_1(reader);
			y = read_proof_1(reader);
			return rtr(x,y);
		//case '#' :
		//	nextchar(reader);
		//	x = read_proof_1(reader);
		//	y = read_proof_1(reader);
		//	return equ(x,y);
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
			if (cur_char == '|')
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
		default :
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
		case RSL :
			putstring_to_printer(printer, "$");
			print_proof_1(printer, x->sp1, 1);
			break;
		case RSR :
			putstring_to_printer(printer, "&");
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
		
void print_proof_to_stdout (proof x) {
	struct printer printer;
	print_to_stdout(&printer);
	print_proof_1(&printer,x,0);
}


void dump () {
	int i;
	for (i=0; i<nproofs; i++) {
		printf("%8lx %c %-8s %8lx %8lx\n", 
			(unsigned long)(proofs+i), 
			proofs[i].op, 
			proofs[i].name, 
			(unsigned long)(proofs[i].sp1), 
			(unsigned long)(proofs[i].sp2));
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
		x = read_proof_from_string(buf);
		printf("%8lx ",(unsigned long)x);
		simple_print_proof(x);
		printf(" ");
		print_proof_to_stdout(x);
		printf("\n\n");
	}
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
	proof x;
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
		print_proof_to_stdout(x);
		printf("\nproves\n");
		print_proof_to_stdout(left(x));
		printf("\nequals\n");
		print_proof_to_stdout(right(x));
		printf("\n");
		fclose(f);
		return 0;
	}
	for (;;) {
		printf("? ");
		//fgets(buf, sizeof(buf), stdin);
		//strcat(buf,".");
		//x = read_proof_from_string(buf);
		x = read_proof_from_stdin();
		if (x == NULL) break;
		print_proof_to_stdout(x);
		printf ("\nreduces to\n");
		print_proof_to_stdout(reduce(x));
		printf ("\nand proves\n");
		//printf("\nproves\n");
		print_proof_to_stdout(left(x));
		printf ("\nequals\n");
		print_proof_to_stdout(right(x));
		printf("\n");
	}
}

