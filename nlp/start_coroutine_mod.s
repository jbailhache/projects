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
	.file	"start_coroutine.c"
	.text
	.align	2
	.global	start_coroutine
	.syntax unified
	.arm
	.fpu vfp
	.type	start_coroutine, %function
start_coroutine:
	@ args = 0, pretend = 0, frame = 32
	@ frame_needed = 1, uses_anonymous_args = 0
	push	{fp, lr}
	add	fp, sp, #4
	sub	sp, sp, #32
	str	r0, [fp, #-24]
	str	r1, [fp, #-28]
	str	r2, [fp, #-32]
	str	r3, [fp, #-36]
	ldr	r3, [fp, #-24]
	ldr	r3, [r3]
	mov	r0, r3
	bl	_setjmp
	str	r0, [fp, #-8]
	ldr	r3, [fp, #-8]
	cmp	r3, #0
	bne	.L5
//	mov	r3, #123
//	str	r3, [fp, #-12]
	ldr	sp, [fp, #-12] // sp = stack
//	ldr	r3, [fp, #-36]
//	str	r3, [fp, #-16]
//	mov	r3, #456
//	str	r3, [fp, #-12]
	ldr	r3, [fp, #-28]
	ldr	r1, [fp, #-24]
	ldr	r0, [fp, #-32]
	blx	r3
	mov	r3, r0
	str	r3, [fp, #-20]
	ldr	r3, [fp, #-20]
	b	.L4
.L5:
	ldr	r3, [fp, #-8]
.L4:
	mov	r0, r3
	sub	sp, fp, #4
	@ sp needed
	pop	{fp, pc}
	.size	start_coroutine, .-start_coroutine
	.ident	"GCC: (Raspbian 6.3.0-18+rpi1+deb9u1) 6.3.0 20170516"
	.section	.note.GNU-stack,"",%progbits
