   
dual1 =: 4 : 0
 < (x,0) ,: (y,x)
)

dual =: 4 : 0
 < (x * (i. 1+#y) =/ i. 1+#y) + |: (0,y),((#y),1+#y)$0
)

echo 3 5 +/ . * 3 5

a =: (3 dual1 1) , (5 dual1 1)
echo a

dplus =: (4 : '< (>x) + (>y)')"0 0
 
dtimes =: (4 : '< (>x) +/ . * (>y)')"0 0

echo dplus/ a dtimes a

echo a dplus/ . dtimes a

echo a dplus/ @ (dtimes"(1,_)) a

f =: 3 : 0
 (y dtimes y) dplus ((3 dual1 0) dtimes y) dplus (5 dual1 0)
)

echo f (6 dual1 1)

g =: 4 : 0
 (x dtimes y) dplus ((3 dual 0 0) dtimes x) dplus ((5 dual 0 0) dtimes y)
)

echo (10 dual 1 0) g (20 dual 0 1)

