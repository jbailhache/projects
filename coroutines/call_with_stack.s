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
	.file	"call_with_stack.c"
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
	.global	f
	.syntax unified
	.arm
	.fpu vfp
	.type	f, %function
f:
	@ args = 0, pretend = 0, frame = 8
	@ frame_needed = 1, uses_anonymous_args = 0
	@ link register save eliminated.
	str	fp, [sp, #-4]!
	add	fp, sp, #0
	sub	sp, sp, #12
	str	r0, [fp, #-8]
	ldr	r3, [fp, #-8]
	lsl	r3, r3, #1
	add	r3, r3, #1
	mov	r0, r3
	add	sp, fp, #0
	@ sp needed
	ldr	fp, [sp], #4
	bx	lr
	.size	f, .-f
	.section	.rodata
	.align	2
.LC0:
	.ascii	"a=%d\012\000"
	.text
	.align	2
	.global	main
	.syntax unified
	.arm
	.fpu vfp
	.type	main, %function
main:
	@ args = 0, pretend = 0, frame = 4040
	@ frame_needed = 1, uses_anonymous_args = 0
	push	{fp, lr}
	add	fp, sp, #4
	sub	sp, sp, #4032
	sub	sp, sp, #8
	sub	r3, fp, #4032
	sub	r3, r3, #4
	sub	r3, r3, #4
	add	r3, r3, #4000
	mov	r2, #123
	ldr	r1, .L9
	mov	r0, r3
	bl	call_with_stack
	str	r0, [fp, #-8]
	ldr	r1, [fp, #-8]
	ldr	r0, .L9+4
	bl	printf
	mov	r3, #0
	mov	r0, r3
	sub	sp, fp, #4
	@ sp needed
	pop	{fp, pc}
.L10:
	.align	2
.L9:
	.word	f
	.word	.LC0
	.size	main, .-main
	.ident	"GCC: (Raspbian 6.3.0-18+rpi1+deb9u1) 6.3.0 20170516"
	.section	.note.GNU-stack,"",%progbits
