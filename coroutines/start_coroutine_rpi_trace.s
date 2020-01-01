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
	.file	"start_coroutine_rpi_trace.c"
	.comm	_SP,4,4
	.section	.rodata
	.align	2
.LC0:
	.ascii	"start_coroutine(0x%X,0x%X,0x%X,0x%X)\012\000"
	.align	2
.LC1:
	.ascii	"x=0x%X\012\000"
	.align	2
.LC2:
	.ascii	"then\000"
	.align	2
.LC3:
	.ascii	"sp modified, call function\000"
	.align	2
.LC4:
	.ascii	"y=0x%X\012\000"
	.align	2
.LC5:
	.ascii	"else\000"
	.text
	.align	2
	.global	start_coroutine
	.syntax unified
	.arm
	.fpu vfp
	.type	start_coroutine, %function
start_coroutine:
	@ args = 0, pretend = 0, frame = 24
	@ frame_needed = 1, uses_anonymous_args = 0
	push	{fp, lr}
	add	fp, sp, #4
	sub	sp, sp, #32
	str	r0, [fp, #-16]
	str	r1, [fp, #-20]
	str	r2, [fp, #-24]
	str	r3, [fp, #-28]
	ldr	r3, [fp, #-28]
	str	r3, [sp]
	ldr	r3, [fp, #-24]
	ldr	r2, [fp, #-20]
	ldr	r1, [fp, #-16]
	ldr	r0, .L5
	bl	printf
	ldr	r3, [fp, #-16]
	ldr	r3, [r3]
	mov	r0, r3
	bl	_setjmp
	str	r0, [fp, #-8]
	ldr	r1, [fp, #-8]
	ldr	r0, .L5+4
	bl	printf
	ldr	r3, [fp, #-8]
	cmp	r3, #0
	bne	.L3
	ldr	r0, .L5+8
	bl	puts
	ldr	r3, [fp, #-28]
	ldr	r2, .L5+12
	str	r3, [r2]
	ldr	r0, .L5+16
	bl	puts
	ldr	r3, [fp, #-20]
	ldr	r1, [fp, #-16]
	ldr	r0, [fp, #-24]
	blx	r3
	mov	r3, r0
	str	r3, [fp, #-12]
	ldr	r1, [fp, #-12]
	ldr	r0, .L5+20
	bl	printf
	ldr	r3, [fp, #-12]
	b	.L4
.L3:
	ldr	r0, .L5+24
	bl	puts
	ldr	r3, [fp, #-8]
.L4:
	mov	r0, r3
	sub	sp, fp, #4
	@ sp needed
	pop	{fp, pc}
.L6:
	.align	2
.L5:
	.word	.LC0
	.word	.LC1
	.word	.LC2
	.word	_SP
	.word	.LC3
	.word	.LC4
	.word	.LC5
	.size	start_coroutine, .-start_coroutine
	.ident	"GCC: (Raspbian 6.3.0-18+rpi1+deb9u1) 6.3.0 20170516"
	.section	.note.GNU-stack,"",%progbits
