	.arch armv6
	.eabi_attribute 28, 1
	.eabi_attribute 20, 1
	.eabi_attribute 21, 1
	.eabi_attribute 23, 3
	.eabi_attribute 24, 1
	.eabi_attribute 25, 1
	.eabi_attribute 26, 2
	.eabi_attribute 30, 6
	.eabi_attribute 34, 1
	.eabi_attribute 18, 4
	.file	"coroutines_my_std.c"
	.text
	.align	2
	.global	getsp
	.syntax unified
	.arm
	.fpu vfp
	.type	getsp, %function
getsp:
	@ args = 0, pretend = 0, frame = 8
	@ frame_needed = 1, uses_anonymous_args = 0
	@ link register save eliminated.
	str	fp, [sp, #-4]!
	add	fp, sp, #0
	sub	sp, sp, #12
	sub	r3, fp, #8
	str	r3, [fp, #-8]
	ldr	r3, [fp, #-8]
	add	r3, r3, #12
	str	r3, [fp, #-8]
	ldr	r3, [fp, #-8]
	mov	r0, r3
	add	sp, fp, #0
	@ sp needed
	ldr	fp, [sp], #4
	bx	lr
	.size	getsp, .-getsp
	.align	2
	.global	call_with_stack
	.syntax unified
	.arm
	.fpu vfp
	.type	call_with_stack, %function
call_with_stack:
	@ args = 0, pretend = 0, frame = 32
	@ frame_needed = 1, uses_anonymous_args = 0
	push	{r4, r5, r6, r7, r8, fp, lr}
	add	fp, sp, #24
	sub	sp, sp, #36
	str	r0, [fp, #-48]
	str	r1, [fp, #-52]
	str	r2, [fp, #-56]
	bl	getsp
	str	r0, [fp, #-32]
	mov	r3, sp
	mov	r8, r3
	ldr	r2, [fp, #-32]
	ldr	r3, [fp, #-48]
	sub	r3, r2, r3
	asr	r3, r3, #2
	mov	r1, r3
	sub	r3, r1, #1
	str	r3, [fp, #-36]
	mov	r3, r1
	mov	r2, r3
	mov	r3, #0
	lsl	r7, r3, #5
	orr	r7, r7, r2, lsr #27
	lsl	r6, r2, #5
	mov	r3, r1
	mov	r2, r3
	mov	r3, #0
	lsl	r5, r3, #5
	orr	r5, r5, r2, lsr #27
	lsl	r4, r2, #5
	mov	r3, r1
	lsl	r3, r3, #2
	add	r3, r3, #3
	add	r3, r3, #7
	lsr	r3, r3, #3
	lsl	r3, r3, #3
	sub	sp, sp, r3
	mov	r3, sp
	add	r3, r3, #3
	lsr	r3, r3, #2
	lsl	r3, r3, #2
	str	r3, [fp, #-40]
	ldr	r3, [fp, #-52]
	ldr	r0, [fp, #-56]
	blx	r3
	mov	r3, r0
	mov	sp, r8
	mov	r0, r3
	sub	sp, fp, #24
	@ sp needed
	pop	{r4, r5, r6, r7, r8, fp, pc}
	.size	call_with_stack, .-call_with_stack
	.align	2
	.global	start
	.syntax unified
	.arm
	.fpu vfp
	.type	start, %function
start:
	@ args = 4, pretend = 0, frame = 48
	@ frame_needed = 1, uses_anonymous_args = 0
	push	{r4, fp, lr}
	add	fp, sp, #8
	sub	sp, sp, #52
	str	r0, [fp, #-32]
	str	r1, [fp, #-36]
	str	r2, [fp, #-40]
	str	r3, [fp, #-44]
	ldr	r0, [fp, #-32]
	bl	_setjmp
	str	r0, [fp, #-16]
	ldr	r3, [fp, #-16]
	cmp	r3, #0
	bne	.L9
	bl	getsp
	mov	r3, r0
	str	r3, [fp, #-20]
	mov	r3, sp
	mov	r4, r3
	ldr	r2, [fp, #-20]
	ldr	r3, [fp, #4]
	sub	r3, r2, r3
	asr	r3, r3, #2
	mov	r1, r3
	sub	r3, r1, #1
	str	r3, [fp, #-24]
	mov	r3, r1
	mov	r2, r3
	mov	r3, #0
	lsl	r0, r3, #5
	str	r0, [fp, #-48]
	ldr	r0, [fp, #-48]
	orr	r0, r0, r2, lsr #27
	str	r0, [fp, #-48]
	lsl	r3, r2, #5
	str	r3, [fp, #-52]
	mov	r3, r1
	mov	r2, r3
	mov	r3, #0
	lsl	r0, r3, #5
	str	r0, [fp, #-56]
	ldr	r0, [fp, #-56]
	orr	r0, r0, r2, lsr #27
	str	r0, [fp, #-56]
	lsl	r3, r2, #5
	str	r3, [fp, #-60]
	mov	r3, r1
	lsl	r3, r3, #2
	add	r3, r3, #3
	add	r3, r3, #7
	lsr	r3, r3, #3
	lsl	r3, r3, #3
	sub	sp, sp, r3
	mov	r3, sp
	add	r3, r3, #3
	lsr	r3, r3, #2
	lsl	r3, r3, #2
	str	r3, [fp, #-28]
	ldr	r3, [fp, #-40]
	ldr	r2, [fp, #-44]
	ldr	r1, [fp, #-36]
	ldr	r0, [fp, #-32]
	blx	r3
	mov	r3, r0
	mov	sp, r4
	b	.L8
.L9:
	ldr	r3, [fp, #-16]
.L8:
	mov	r0, r3
	sub	sp, fp, #8
	@ sp needed
	pop	{r4, fp, pc}
	.size	start, .-start
	.align	2
	.global	cont
	.syntax unified
	.arm
	.fpu vfp
	.type	cont, %function
cont:
	@ args = 0, pretend = 0, frame = 24
	@ frame_needed = 1, uses_anonymous_args = 0
	push	{fp, lr}
	add	fp, sp, #4
	sub	sp, sp, #24
	str	r0, [fp, #-16]
	str	r1, [fp, #-20]
	str	r2, [fp, #-24]
	ldr	r0, [fp, #-16]
	bl	_setjmp
	str	r0, [fp, #-8]
	ldr	r3, [fp, #-8]
	cmp	r3, #0
	bne	.L14
	ldr	r1, [fp, #-24]
	ldr	r0, [fp, #-20]
	bl	longjmp
.L14:
	ldr	r3, [fp, #-8]
	mov	r0, r3
	sub	sp, fp, #4
	@ sp needed
	pop	{fp, pc}
	.size	cont, .-cont
	.section	.rodata
	.align	2
.LC0:
	.ascii	"First got %s from Main\012\000"
	.align	2
.LC1:
	.ascii	"Fine Main, and you ?\000"
	.align	2
.LC2:
	.ascii	"Then got %s from Main\012\000"
	.align	2
.LC3:
	.ascii	"Nice day, isn't it ?\000"
	.align	2
.LC4:
	.ascii	"That's all !\012\000"
	.text
	.align	2
	.global	coroutine_actions
	.syntax unified
	.arm
	.fpu vfp
	.type	coroutine_actions, %function
coroutine_actions:
	@ args = 0, pretend = 0, frame = 24
	@ frame_needed = 1, uses_anonymous_args = 0
	push	{fp, lr}
	add	fp, sp, #4
	sub	sp, sp, #24
	str	r0, [fp, #-16]
	str	r1, [fp, #-20]
	str	r2, [fp, #-24]
	ldr	r3, [fp, #-24]
	mov	r1, r3
	ldr	r0, .L17
	bl	printf
	ldr	r3, .L17+4
	mov	r2, r3
	ldr	r1, [fp, #-16]
	ldr	r0, [fp, #-20]
	bl	cont
	mov	r3, r0
	str	r3, [fp, #-8]
	ldr	r1, [fp, #-8]
	ldr	r0, .L17+8
	bl	printf
	ldr	r3, .L17+12
	mov	r2, r3
	ldr	r1, [fp, #-16]
	ldr	r0, [fp, #-20]
	bl	cont
	mov	r3, r0
	str	r3, [fp, #-8]
	ldr	r3, .L17+16
	mov	r0, r3
	sub	sp, fp, #4
	@ sp needed
	pop	{fp, pc}
.L18:
	.align	2
.L17:
	.word	.LC0
	.word	.LC1
	.word	.LC2
	.word	.LC3
	.word	.LC4
	.size	coroutine_actions, .-coroutine_actions
	.section	.rodata
	.align	2
.LC5:
	.ascii	"Hello Coroutine, how are you ?\000"
	.align	2
.LC6:
	.ascii	"First got %s from Coroutine\012\000"
	.align	2
.LC7:
	.ascii	"And what else ?\000"
	.align	2
.LC8:
	.ascii	"Then got %s from Coroutine\012\000"
	.text
	.align	2
	.global	main
	.syntax unified
	.arm
	.fpu vfp
	.type	main, %function
main:
	@ args = 0, pretend = 0, frame = 4792
	@ frame_needed = 1, uses_anonymous_args = 0
	push	{fp, lr}
	add	fp, sp, #4
	sub	sp, sp, #4800
	ldr	r2, .L21
	sub	r3, fp, #4736
	sub	r3, r3, #4
	sub	r3, r3, #56
	add	r3, r3, #4000
	sub	r1, fp, #796
	sub	r0, fp, #404
	str	r3, [sp]
	mov	r3, r2
	ldr	r2, .L21+4
	bl	start
	mov	r3, r0
	str	r3, [fp, #-8]
	ldr	r1, [fp, #-8]
	ldr	r0, .L21+8
	bl	printf
	ldr	r2, .L21+12
	sub	r1, fp, #796
	sub	r3, fp, #404
	mov	r0, r3
	bl	cont
	mov	r3, r0
	str	r3, [fp, #-8]
	ldr	r1, [fp, #-8]
	ldr	r0, .L21+16
	bl	printf
	mov	r3, #0
	mov	r0, r3
	sub	sp, fp, #4
	@ sp needed
	pop	{fp, pc}
.L22:
	.align	2
.L21:
	.word	.LC5
	.word	coroutine_actions
	.word	.LC6
	.word	.LC7
	.word	.LC8
	.size	main, .-main
	.ident	"GCC: (Raspbian 6.3.0-18+rpi1+deb9u1) 6.3.0 20170516"
	.section	.note.GNU-stack,"",%progbits
