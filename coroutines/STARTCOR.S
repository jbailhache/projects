	.file	"startcor.c"
	.version	"01.01"
gcc2_compiled.:
.text
	.align 16
.globl start_coroutine
	.type	 start_coroutine,@function
start_coroutine:
	pushl %ebp
	movl %esp,%ebp
	subl $16,%esp
	pushl %ebx
	pushl $8
	call malloc
	addl $4,%esp
	movl %eax,-12(%ebp)
	pushl $0
	movl 8(%ebp),%eax
	movl (%eax),%edx
	pushl %edx
	call __sigsetjmp
	addl $8,%esp
	movl %eax,%eax
	movl %eax,-4(%ebp)
	cmpl $0,-4(%ebp)
	jne .L2
	movl -12(%ebp),%eax
	movl 8(%ebp),%edx
	movl 4(%edx),%ecx
	movl %ecx,(%eax)
	movl -12(%ebp),%eax
	movl 8(%ebp),%edx
	movl (%edx),%ecx
	movl %ecx,4(%eax)
	movl $1234,-16(%ebp)
	movl 20(%ebp),%eax
	movl %eax,%esp
	movl -12(%ebp),%eax
	pushl %eax
	movl 16(%ebp),%eax
	pushl %eax
	movl 12(%ebp),%ebx
	call *%ebx
	addl $8,%esp
	movl %eax,%eax
	movl %eax,-8(%ebp)
	jmp .L3
	.align 16
.L2:
	movl -4(%ebp),%eax
	jmp .L1
	.align 16
.L3:
.L1:
	movl -20(%ebp),%ebx
	movl %ebp,%esp
	popl %ebp
	ret
.Lfe1:
	.size	 start_coroutine,.Lfe1-start_coroutine
	.ident	"GCC: (GNU) 2.7.2.3"
