	.arch armv7-a
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
	.file	"start_coroutine_android.c"
	.text
	.comm	_SP,4,4
	.align	1
	.global	start_coroutine
	.arch armv7-a
	.syntax unified
	.thumb
	.thumb_func
	.fpu vfpv3-d16
	.type	start_coroutine, %function
start_coroutine:
	@ args = 0, pretend = 0, frame = 32
	@ frame_needed = 1, uses_anonymous_args = 0
	push	{r7, lr}
	sub	sp, sp, #32
	add	r7, sp, #0
	str	r0, [r7, #20]
	str	r1, [r7, #16]
	str	r2, [r7, #12]
	str	r3, [r7, #8]
	ldr	r3, .L5
.LPIC0:
	add	r3, pc
	str	r3, [r7, #4]
	ldr	r3, [r7, #20]
	ldr	r3, [r3]
	mov	r0, r3
	bl	_setjmp(PLT)
	mov	r3, r0
	str	r3, [r7, #28]
	ldr	r3, [r7, #28]
	cmp	r3, #0
	bne	.L3
	ldr	r3, [r7, #8]
	ldr	r2, .L5+4
	ldr	r1, [r7, #4]
	ldr	r2, [r1, r2]
	str	r3, [r2]
	ldr	r3, [r7, #16]
	ldr	r1, [r7, #20]
	ldr	r0, [r7, #12]
	blx	r3
	mov	r3, r0
	str	r3, [r7, #24]
	ldr	r3, [r7, #24]
	b	.L4
.L3:
	ldr	r3, [r7, #28]
.L4:
	mov	r0, r3
	adds	r7, r7, #32
	mov	sp, r7
	@ sp needed
	pop	{r7, pc}
.L6:
	.align	2
.L5:
	.word	_GLOBAL_OFFSET_TABLE_-(.LPIC0+4)
	.word	_SP(GOT)
	.size	start_coroutine, .-start_coroutine
	.ident	"GCC: (Debian 8.3.0-6) 8.3.0"
	.section	.note.GNU-stack,"",%progbits
