
NB. https://code.jsoftware.com/wiki/Vocabulary/dot
NB.  x u . v y is also defined for other cases, where the arguments are not tables or u and v have different forms or ranks, as x u@(v"(1+lv,_)) y, where lv is the left rank of dyadic v. 

a1 =: < 2 2 $ 3 0 1 3
a2 =: < 2 2 $ 5 0 1 5
a =: a1 , a2

p =: 4 : 0
 < (>x) + (>y)
)
 
t =: 4 : 0
 < (>x) +/ . * (>y)
)

echo a p/ . t"0 0 a

echo a p/ @ ((t"0 0)"(1,_)) a
