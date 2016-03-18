41 EMIT
41 1 + EMIT
40 3 + EMIT
49 5 - EMIT
45 SP@ @ EMIT
: f 6 [ 46 EMIT ] + ;
41 f EMIT
: g 48 EMIT ; IMMEDIATE
: h 7 g + ;
42 h EMIT
VARIABLE a
40 a !
0A a @ + EMIT
: k 0B + ; IMMEDIATE
: l 40 [COMPILE] k EMIT ;
l
: aaa 4C EMIT ;
: bbb 4D EMIT ;
: ccc COMPILE bbb aaa ; IMMEDIATE
: ddd ccc ;
ddd
0A EMIT 0D EMIT
BYE

