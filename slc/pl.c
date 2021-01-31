
#include <stdlib.h>
#include <stdio.h>
#include <string.h>


struct reader {
	char (*getchar)(struct reader *);
	void *p;
};

char getchar_from_reader (struct reader *reader) {
	return (*(reader->getchar))(reader);
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
	proof sp1, sp2, red, left, right;	
};

#define MAXPROOFS 1000

int nproofs;

struct proof proofs[MAXPROOFS];

void init() {
	nproofs = 0;
	proofs[nproofs].op = VAR;
	proofs[nproofs].red = proofs+nproofs;
	proofs[nproofs].left = proofs+nproofs;
	proofs[nproofs].right = proofs+nproofs;
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
	proofs[nproofs].left = NULL;
	proofs[nproofs].right = NULL;
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
				if (strchr(" \t\n\r()*'\\[]-/%{,}<|>#=",cur_char)) break;
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
	read_from_string(&reader,s);
	cur_char = getchar_from_reader(&reader);
	return read_proof_1(&reader);
}


void dump () {
	int i;
	for (i=0; i<nproofs; i++) {
		printf("%8x %c %-8s %8x %8x\n", proofs+i, proofs[i].op, proofs[i].name, proofs[i].sp1, proofs[i].sp2);
	}
}

int main() {
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
		printf("\n\n");
	}
}
