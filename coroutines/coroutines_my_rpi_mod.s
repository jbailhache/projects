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
	.file	"coroutines_my_rpi.c"
	.text
	.align	2
	.global	start
	.syntax unified
	.arm
	.fpu vfp
	.type	start, %function
start:
	@ args = 4, pretend = 0, frame = 24
	@ frame_needed = 1, uses_anonymous_args = 0
	push	{fp, lr}
	add	fp, sp, #4
	sub	sp, sp, #24
	str	r0, [fp, #-16]
	str	r1, [fp, #-20]
	str	r2, [fp, #-24]
	str	r3, [fp, #-28]
	ldr	r0, [fp, #-16]
	bl	_setjmp
	str	r0, [fp, #-8]
	ldr	r3, [fp, #-8]
	cmp	r3, #0
	bne	.L5

	ldr	sp, [fp, #4]

	ldr	r3, [fp, #-24]
	ldr	r2, [fp, #-28]
	ldr	r1, [fp, #-20]
	ldr	r0, [fp, #-16]
	blx	r3
	mov	r3, r0
	b	.L4
.L5:
	ldr	r3, [fp, #-8]
.L4:
	mov	r0, r3
	sub	sp, fp, #4
	@ sp needed
	pop	{fp, pc}
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
	bne	.L10
	ldr	r1, [fp, #-24]
	ldr	r0, [fp, #-20]
	bl	longjmp
.L10:
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
	ldr	r0, .L13
	bl	printf
	ldr	r3, .L13+4
	mov	r2, r3
	ldr	r1, [fp, #-16]
	ldr	r0, [fp, #-20]
	bl	cont
	mov	r3, r0
	str	r3, [fp, #-8]
	ldr	r1, [fp, #-8]
	ldr	r0, .L13+8
	bl	printf
	ldr	r3, .L13+12
	mov	r2, r3
	ldr	r1, [fp, #-16]
	ldr	r0, [fp, #-20]
	bl	cont
	mov	r3, r0
	str	r3, [fp, #-8]
	ldr	r3, .L13+16
	mov	r0, r3
	sub	sp, fp, #4
	@ sp needed
	pop	{fp, pc}
.L14:
	.align	2
.L13:
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
	ldr	r2, .L17
	sub	r3, fp, #4736
	sub	r3, r3, #4
	sub	r3, r3, #56
	add	r3, r3, #4000
	sub	r1, fp, #796
	sub	r0, fp, #404
	str	r3, [sp]
	mov	r3, r2
	ldr	r2, .L17+4
	bl	start
	mov	r3, r0
	str	r3, [fp, #-8]
	ldr	r1, [fp, #-8]
	ldr	r0, .L17+8
	bl	printf
	ldr	r2, .L17+12
	sub	r1, fp, #796
	sub	r3, fp, #404
	mov	r0, r3
	bl	cont
	mov	r3, r0
	str	r3, [fp, #-8]
	ldr	r1, [fp, #-8]
	ldr	r0, .L17+16
	bl	printf
	mov	r3, #0
	mov	r0, r3
	sub	sp, fp, #4
	@ sp needed
	pop	{fp, pc}
.L18:
	.align	2
.L17:
	.word	.LC5
	.word	coroutine_actions
	.word	.LC6
	.word	.LC7
	.word	.LC8
	.size	main, .-main
	.ident	"GCC: (Raspbian 6.3.0-18+rpi1+deb9u1) 6.3.0 20170516"
	.section	.note.GNU-stack,"",%progbits
