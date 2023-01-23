   
dual =: 3 : 0
 < (y,0),:(1,y)
:
 < (y,0),:(x,y)
)

echo 3 5 +/ . * 3 5

a =: (dual 3) , (dual 5)
echo a

dplus =: 4 : 0
 < (>x) + (>y)
)
 
dtimes1 =: 4 : 0
 < (>x) +/ . * (>y)
)

dtimes =: dtimes1"0 0

echo dplus/ a dtimes a

echo a dplus/ . dtimes a

echo a dplus/ @ (dtimes"(1,_)) a
