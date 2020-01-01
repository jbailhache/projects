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
	.file	"start_coroutine_rpi.c"
	.comm	_SP,4,4
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
	sub	sp, sp, #24
	str	r0, [fp, #-16]
	str	r1, [fp, #-20]
	str	r2, [fp, #-24]
	str	r3, [fp, #-28]
	ldr	r3, [fp, #-16]
	ldr	r3, [r3]
	mov	r0, r3
	bl	_setjmp
	str	r0, [fp, #-8]
	ldr	r3, [fp, #-8]
	cmp	r3, #0
	bne	.L5
	ldr	sp, [fp, #-28]	// sp = stack
//	ldr	r3, [fp, #-28]
//	ldr	r2, .L6
//	str	r3, [r2]
	ldr	r3, [fp, #-20]
	ldr	r1, [fp, #-16]
	ldr	r0, [fp, #-24]
	blx	r3
	mov	r3, r0
	str	r3, [fp, #-12]
	ldr	r3, [fp, #-12]
	b	.L4
.L5:
	ldr	r3, [fp, #-8]
.L4:
	mov	r0, r3
	sub	sp, fp, #4
	@ sp needed
	pop	{fp, pc}
.L7:
	.align	2
.L6:
	.word	_SP
	.size	start_coroutine, .-start_coroutine
	.ident	"GCC: (Raspbian 6.3.0-18+rpi1+deb9u1) 6.3.0 20170516"
	.section	.note.GNU-stack,"",%progbits
