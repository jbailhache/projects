# cat start_coroutine.s
        .verstamp       2 0
        .text   
        .align  2
        .file   2 "start_coroutine.c"
        .globl  start_coroutine
        .loc    2 13
 #  13  {
        .ent    start_coroutine 2
start_coroutine:
        .option O1
        subu    $sp, 40
        sw      $31, 20($sp)
        sd      $4, 40($sp)
        sd      $6, 48($sp)
        .mask   0x80000000, -20
        .frame  $sp, 40, $31
        .loc    2 17
 #  14  int x, y;
 #  15  struct coroutine *calling;
 #  16  int *test;
 #  17      calling = malloc (sizeof (*calling));
        li      $4, 8
        jal     malloc
        sw      $2, 28($sp)
        .loc    2 18
 #  18      x = setjmp (*(cr->calling));
        lw      $14, 40($sp)
        lw      $4, 0($14)
        jal     setjmp
        sw      $2, 36($sp)
        .loc    2 19
 #  19      if (x == 0)
        lw      $15, 36($sp)
        bne     $15, 0, $32
        .loc    2 21
 #  20      {
 #  21          calling->calling = cr->env;
        lw      $24, 40($sp)
        lw      $25, 4($24)
        lw      $8, 28($sp)
        sw      $25, 0($8)
        .loc    2 22
 #  22          calling->env = cr->calling;
        lw      $9, 40($sp)
        lw      $10, 0($9)
        lw      $11, 28($sp)
        sw      $10, 4($11)
        .loc    2 23
 #  23          test = stack;   
        lw      $12, 52($sp)
        sw      $12, 24($sp)
        .loc    2 24
 #  24          y = (*f) (p, calling);
        lw      $4, 48($sp)
        lw      $5, 28($sp)
        lw      $13, 44($sp)
        lw      $sp, 52($sp)
        jal     $13
        sw      $2, 32($sp)
        .loc    2 25
 #  25      }
        b       $33
$32:
        .loc    2 27
 #  26      else
 #  27          return x;
        lw      $2, 36($sp)
$33:
        lw      $31, 20($sp)
        addu    $sp, 40
        j       $31
        .end    start_coroutine
