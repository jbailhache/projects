   
dual =: 4 : 0
 < (x,0) ,: (y,x)
)

echo 3 5 +/ . * 3 5

a =: (3 dual 1) , (5 dual 1)
echo a

dplus =: (4 : '< (>x) + (>y)')"0 0
 
dtimes =: (4 : '< (>x) +/ . * (>y)')"0 0

echo dplus/ a dtimes a

echo a dplus/ . dtimes a

echo a dplus/ @ (dtimes"(1,_)) a

f =: 3 : 0
 (y dtimes y) dplus ((3 dual 0) dtimes y) dplus (5 dual 0)
)

echo f (6 dual 1)

