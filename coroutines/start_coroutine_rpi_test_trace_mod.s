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
	.file	"start_coroutine_rpi_test_trace.c"
	.section	.rodata
	.align	2
.LC0:
	.ascii	"start_coroutine(0x%X,0x%X,0x%X,0x%X)\012\000"
	.align	2
.LC1:
	.ascii	"calling=0x%X\012\000"
	.align	2
.LC2:
	.ascii	"x=0x%X\012\000"
	.align	2
.LC3:
	.ascii	"then\000"
	.align	2
.LC4:
	.ascii	"set sp\000"
	.align	2
.LC5:
	.ascii	"sp modified, call function\000"
	.align	2
.LC6:
	.ascii	"y=0x%X\012\000"
	.align	2
.LC7:
	.ascii	"else\000"
	.text
	.align	2
	.global	start_coroutine
	.syntax unified
	.arm
	.fpu vfp
	.type	start_coroutine, %function
start_coroutine:
	@ args = 0, pretend = 0, frame = 40
	@ frame_needed = 1, uses_anonymous_args = 0
	push	{fp, lr}
	add	fp, sp, #4
	sub	sp, sp, #48
	str	r0, [fp, #-32]
	str	r1, [fp, #-36]
	str	r2, [fp, #-40]
	str	r3, [fp, #-44]
	ldr	r3, [fp, #-44]
	str	r3, [sp]
	ldr	r3, [fp, #-40]
	ldr	r2, [fp, #-36]
	ldr	r1, [fp, #-32]
	ldr	r0, .L5
	bl	printf
	mov	r0, #8
	bl	malloc
	mov	r3, r0
	str	r3, [fp, #-8]
	ldr	r1, [fp, #-8]
	ldr	r0, .L5+4
	bl	printf
	ldr	r3, [fp, #-32]
	ldr	r3, [r3]
	mov	r0, r3
	bl	_setjmp
	str	r0, [fp, #-12]
	ldr	r1, [fp, #-12]
	ldr	r0, .L5+8
	bl	printf
	ldr	r3, [fp, #-12]
	cmp	r3, #0
	bne	.L3
	ldr	r0, .L5+12
	bl	puts
	ldr	r3, [fp, #-32]
	ldr	r2, [r3, #4]
	ldr	r3, [fp, #-8]
	str	r2, [r3]
	ldr	r3, [fp, #-32]
	ldr	r2, [r3]
	ldr	r3, [fp, #-8]
	str	r2, [r3, #4]
	ldr	r0, .L5+16
	bl	puts

	ldr	sp, [fp, #-44]

	ldr	r0, .L5+20
	bl	puts
	ldr	r3, [fp, #-36]
	ldr	r1, [fp, #-32]
	ldr	r0, [fp, #-40]
	blx	r3
	mov	r3, r0
	str	r3, [fp, #-24]
	ldr	r1, [fp, #-24]
	ldr	r0, .L5+24
	bl	printf
	ldr	r3, [fp, #-24]
	b	.L4
.L3:
	ldr	r0, .L5+28
	bl	puts
	ldr	r3, [fp, #-12]
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
	.word	.LC3
	.word	.LC4
	.word	.LC5
	.word	.LC6
	.word	.LC7
	.size	start_coroutine, .-start_coroutine
	.ident	"GCC: (Raspbian 6.3.0-18+rpi1+deb9u1) 6.3.0 20170516"
	.section	.note.GNU-stack,"",%progbits
