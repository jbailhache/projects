	.file	"startco.c"
	.version	"01.01"
gcc2_compiled.:
.text
	.align 16
.globl start_coroutine
	.type	 start_coroutine,@function
start_coroutine:
	pushl %ebp
	movl %esp,%ebp
	subl $12,%esp
	pushl %ebx
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
	movl $4660,-12(%ebp)
	movl 20(%ebp),%eax
	movl %eax,%esp
	movl 8(%ebp),%eax
	pushl %eax
	movl 16(%ebp),%eax
	pushl %eax
	movl 12(%ebp),%ebx
	call *%ebx
	addl $8,%esp
	movl %eax,%eax
	movl %eax,-8(%ebp)
	movl -8(%ebp),%eax
	jmp .L1
	.align 16
	jmp .L3
	.align 16
.L2:
	movl -4(%ebp),%eax
	jmp .L1
	.align 16
.L3:
.L1:
	movl -16(%ebp),%ebx
	movl %ebp,%esp
	popl %ebp
	ret
.Lfe1:
	.size	 start_coroutine,.Lfe1-start_coroutine
	.ident	"GCC: (GNU) 2.7.2.3"
