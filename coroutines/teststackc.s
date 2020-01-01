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
	.file	"teststackc.c"
	.text
	.align	2
	.global	g
	.syntax unified
	.arm
	.fpu vfp
	.type	g, %function
g:
	@ args = 0, pretend = 0, frame = 16
	@ frame_needed = 1, uses_anonymous_args = 0
	@ link register save eliminated.
	str	fp, [sp, #-4]!
	add	fp, sp, #0
	sub	sp, sp, #20
	str	r0, [fp, #-16]
	ldr	r3, [fp, #-16]
	str	r3, [fp, #-8]
	ldr	r3, [fp, #-8]
	lsl	r3, r3, #1
	add	r3, r3, #1
	str	r3, [fp, #-8]
	ldr	r3, [fp, #-8]
	mov	r0, r3
	add	sp, fp, #0
	@ sp needed
	ldr	fp, [sp], #4
	bx	lr
	.size	g, .-g
	.align	2
	.global	f
	.syntax unified
	.arm
	.fpu vfp
	.type	f, %function
f:
	@ args = 0, pretend = 0, frame = 24
	@ frame_needed = 1, uses_anonymous_args = 0
	push	{r4, r5, r6, fp, lr}
	add	fp, sp, #16
	sub	sp, sp, #28
	str	r0, [fp, #-40]
	str	r1, [fp, #-44]
	ldr	r1, [fp, #-40]
	str	r1, [fp, #-24]
	mov	r1, sp
	mov	r6, r1
	ldr	ip, [fp, #-24]
	sub	r1, ip, #1
	str	r1, [fp, #-28]
	mov	r1, ip
	mov	r0, r1
	mov	r1, #0
	lsl	r5, r1, #3
	orr	r5, r5, r0, lsr #29
	lsl	r4, r0, #3
	mov	r1, ip
	mov	r0, r1
	mov	r1, #0
	lsl	r3, r1, #3
	orr	r3, r3, r0, lsr #29
	lsl	r2, r0, #3
	mov	r3, ip
	add	r3, r3, #7
	lsr	r3, r3, #3
	lsl	r3, r3, #3
	sub	sp, sp, r3
	mov	r3, sp
	add	r3, r3, #0
	str	r3, [fp, #-32]
	ldr	r0, [fp, #-44]
	bl	g
	str	r0, [fp, #-36]
	mov	sp, r6
	ldr	r3, [fp, #-36]
	mov	r0, r3
	sub	sp, fp, #16
	@ sp needed
	pop	{r4, r5, r6, fp, pc}
	.size	f, .-f
	.align	2
	.global	main
	.syntax unified
	.arm
	.fpu vfp
	.type	main, %function
main:
	@ args = 0, pretend = 0, frame = 16
	@ frame_needed = 1, uses_anonymous_args = 0
	push	{fp, lr}
	add	fp, sp, #4
	sub	sp, sp, #16
	mov	r3, #256
	str	r3, [fp, #-8]
	mov	r3, #123
	str	r3, [fp, #-12]
	ldr	r1, [fp, #-12]
	ldr	r0, [fp, #-8]
	bl	f
	str	r0, [fp, #-16]
	mov	r3, #0
	mov	r0, r3
	sub	sp, fp, #4
	@ sp needed
	pop	{fp, pc}
	.size	main, .-main
	.ident	"GCC: (Raspbian 6.3.0-18+rpi1+deb9u1) 6.3.0 20170516"
	.section	.note.GNU-stack,"",%progbits
