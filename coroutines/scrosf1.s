	.ugen
	.verstamp	3 11
	.text
	.align	4
	.file	2 "start_coroutine.c"
	.globl	"start_coroutine"
	.loc	2 13
 #   13 {
	.ent	start_coroutine 2
start_coroutine:
	.option 01
	ldgp	$gp, 0($27)
	lda	$sp, -96($sp)
	stq 	$26, 0($sp)
	stq     $16, 48($sp)
	stq	$17, 56($sp)
	stq	$18, 64($sp)
	stq	$19, 72($sp)
	.mask	0x04000000, -96
	.frame	$sp, 96, $26, 48
	.prologue
	.loc	2 13

	.loc	2 19
 #   14 int x, y;
 #   15 /*
 #   16 struct coroutine calling;
 #   17 */
 #   18 int *test;
 #   19	    x = setjmp (*(cr->calling));
	ldq	$1, 48($sp)
	ldq	$16, 0($1)
	.livereg	0x0001C002,0x00000000
	jsr	$26, setjmp
	ldgp	$gp, 0($26)
	stl	$0, 40($sp)
	.loc	2 20
 #   20     if (x == 0)
	ldl	$2, 40($sp)
	bne	$2, $32
	.loc	2 21
 #   21     {
	.loc	2 26
 #   22 /*
 #   23		calling.calling = cr->env;
 #   24		calling->env = cr->calling;
 #   25 */
 #   26 	test = stack;
	ldq	$3, 72($sp)
	stq	$3, 24($sp)
	.loc	2 27
 #   27		y = (*f) (p, cr);
	ldq	$16, 64($sp)
	ldq	$17, 48($sp)
	.livereg	0x0001E002,0x00000000
	ldq	$27, 56($sp)
	ldq	$sp, 72($sp)
	jsr	$26, ($27), 0
	ldgp	$gp, 0($26)
	stl	$0, 32($sp)
	br	$31, $33
$32:
	.loc	2 30
 #   28    }
 #   29    else
 #   30 	return x;
	ldl $0, 40($sp)
$33:
	.livereg	0xFC7F0002,0x3FC00000
	ldq	$26, 0($sp)
	lda	$sp, 96($sp)
	ret	$31, ($26), 1
	.end	start_coroutine


