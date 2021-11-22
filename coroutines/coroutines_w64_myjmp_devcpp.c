/* coroutines */

#include <stdio.h>

#define MLS(a) #a 

#define NREGS 18

typedef __int64 myjmp_buf[NREGS];

__int64 mysetjmp (myjmp_buf env)
{
	asm (" \
		movq	16(%rbp), %rax;\
		addq	$8, %rax;\
		movq	%rbx, (%rax);\
		\
		movq	16(%rbp), %rax;\
		addq	$16, %rax;\
		movq	%rcx, (%rax);\
		\
		movq	16(%rbp), %rax;\
		addq	$24, %rax;\
		movq	%rdx, (%rax);\
		\
		movq	16(%rbp), %rax;\
		addq	$32, %rax;\
		movq	%rsi, (%rax);\
		\
		movq	16(%rbp), %rax;\
		addq	$40, %rax;\
		movq	%rdi, (%rax);\
		\
		movq	16(%rbp), %rax;\
		addq	$64, %rax;\
		movq	%r8, (%rax);\
		\
		movq	16(%rbp), %rax;\
		addq	$72, %rax;\
		movq	%r9, (%rax);\
		\
		movq	16(%rbp), %rax;\
		addq	$80, %rax;\
		movq	%r10, (%rax);\
		\
		movq	16(%rbp), %rax;\
		addq	$88, %rax;\
		movq	%r11, (%rax);\
		\
		movq	16(%rbp), %rax;\
		addq	$96, %rax;\
		movq	%r12, (%rax);\
		\
		movq	16(%rbp), %rax;\
		addq	$104, %rax;\
		movq	%r13, (%rax);\
		\
		movq	16(%rbp), %rax;\
		addq	$112, %rax;\
		movq	%r14, (%rax);\
		\
		movq	16(%rbp), %rax;\
		addq	$120, %rax;\
		movq	%r15, (%rax);\
		\
		// Stack frame :\
		// %rsp ------------------> ...\
		// ...\
		// %rbp ------------------> %rbp caller\
		// %rbp+8                   %rip caller\
		// %rbp+16 = %rsp caller -> ...\
		// ...\
		// %rbp caller -----------> ...\
		// ...\
		\
		// %rsp caller = %rsp + 2 words = %rsp+16\r\n\
		movq	16(%rbp), %rax;\
		addq	$48, %rax;\
		movq	%rbp, (%rax);\
		addq $16, (%rax);\
		\
		// %rbp caller = (%rbp)\r\n\
		movq	16(%rbp), %rax;\
		addq	$56, %rax;\
		movq	%rbp, %rbx;\
		movq (%rbx), %rbx;\
		movq	%rbx, (%rax);\
		\
		// %rip caller = (%rbp + 1 word) = (%rbp+8)\r\n\
		movq	16(%rbp), %rax;\
		addq	$128, %rax;\
		movq	%rbp, %rbx;\
		addq $8, %rbx;\
		movq (%rbx), %rbx;\
		movq	%rbx, (%rax);\
		");
		return 0;
}

void mylongjmp (myjmp_buf env, __int64 value)
{
__int64 r;
	r = env[1];
	r = env[2];
	r = env[3];
	asm ("\
		movq	16(%rbp), %rax;\
		movq	8(%rax), %rax;\
		movq	%rax, %rbx;\
		\
		movq	16(%rbp), %rax;\
		movq	16(%rax), %rax;\
		movq	%rax, %rcx;\
		\
		movq	16(%rbp), %rax;\
		movq	24(%rax), %rax;\
		movq	%rax, %rdx;\
		\
		movq	16(%rbp), %rax;\
		movq	32(%rax), %rax;\
		movq	%rax, %rsi;\
		\
		movq	16(%rbp), %rax;\
		movq	40(%rax), %rax;\
		movq	%rax, %rdi;\
		\
		movq	16(%rbp), %rax;\
		movq	64(%rax), %rax;\
		movq	%rax, %r8;\
		\
		movq	16(%rbp), %rax;\
		movq	72(%rax), %rax;\
		movq	%rax, %r9;\
		\
		movq	16(%rbp), %rax;\
		movq	80(%rax), %rax;\
		movq	%rax, %r10;\
		\
		movq	16(%rbp), %rax;\
		movq	88(%rax), %rax;\
		movq	%rax, %r11;\
		\
		movq	16(%rbp), %rax;\
		movq	96(%rax), %rax;\
		movq	%rax, %r12;\
		\
		movq	16(%rbp), %rax;\
		movq	104(%rax), %rax;\
		movq	%rax, %r13;\
		\
		movq	16(%rbp), %rax;\
		movq	112(%rax), %rax;\
		movq	%rax, %r14;\
		\
		movq	16(%rbp), %rax;\
		movq	120(%rax), %rax;\
		movq	%rax, %r15;\
		\
		// %rsp\r\n\
		movq	16(%rbp), %rax;\
		movq	48(%rax), %rax;\
		movq	%rax, %rsp;\
		\
		// %rbp\r\n\
		movq	16(%rbp), %rax;\
		movq	56(%rax), %rax;\
		movq	%rax, %rbx;\
		\
		// %rip\r\n\
		movq	16(%rbp), %rax;\
		movq	128(%rax), %rax;\
		push	%rax;\
		\
		// result = value\r\n\
		movq	24(%rbp), %rax;\
		// %rbp\r\n\
		movq	%rbx, %rbp;\
		ret;\
		");
	
}

typedef struct coroutine { myjmp_buf *caller; myjmp_buf *called; } *coroutine;

// int stack[10000];

char *jmpval;

int *getsp ()
{
int *a;
	a = (int *)&a;
	a += 3;
	return a;
}

/*
int call_with_stack (int *stack, int (*f)(), int x)
{
int *sp;
	sp = getsp();
	{
		int buf[sp-stack];
		return (*f) (x);
	}
}
*/

int *savesp;

char *start (coroutine cr, char *(*actions) (), char *intro, int *stack)
{
int result;
int *sp;
char *r;
	result = mysetjmp (*(cr->caller));
	if (result == 0)
	{
		// sp = (int *)123; /*savesp = sp;*/ sp = stack; sp = (int *)456;
		asm ("\
			movq	40(%rbp), %rax;\
			movq	%rax, %rsp;\
		");
		r = (*actions) (cr, intro);
		//sp = (int *)234; sp = savesp; sp = (int *)567
		asm ("\
			movq	%rbp, %rsp;\
			subq	$48, %rsp;\
		");
		return r;
		/*
		sp = getsp();
		{
			int buf[sp-stack];
			return (*actions) (cr, intro);
		}
		*/
	}
	else return jmpval;

}

char *cont (coroutine cr, char *param)
{
int result;
	result = mysetjmp (*(cr->caller));
	if (result == 0) 
	{
		jmpval = param;
		mylongjmp (*(cr->called), 1);
	}
	else return jmpval;
}

char *coroutine_actions (coroutine me, char *intro)
{
struct coroutine you[1];
char *answer;
	you->caller = me->called;
	you->called = me->caller;
	printf ("First got %s from Main\n", intro);
	answer = cont (you, "Fine Main, and you ?");
	printf ("Then got %s from Main\n", answer);
	answer = cont (you, "Nice day, isn't it ?");
	return "That's all !\n";
}

int main ()
{
myjmp_buf my_env, your_env;
struct coroutine cr[1];
char *answer;
#define STACK_SIZE 1000
int stack[STACK_SIZE];
	printf("Test coroutines: main=0x%X stack=0x%X\n", main, stack+STACK_SIZE-100);
	cr->caller = &my_env;
	cr->called = &your_env;
	answer = start (cr, coroutine_actions, "Hello Coroutine, how are you ?", stack+STACK_SIZE-100);
	printf ("First got %s from Coroutine\n", answer);
	answer = cont (cr, "And what else ?");
	printf ("Then got %s from Coroutine\n", answer);
}


		

