   
dual =: 4 : 0
 < (x,0),:(y,x)
)

echo 3 5 +/ . * 3 5

a =: (3 dual 1) , (5 dual 1)
echo a

dplus =: 4 : 0
 < (>x) + (>y)
)
 
dtimes =: 4 : 0
 < (>x) +/ . * (>y)
)

echo dplus/ a dtimes"0 a

echo a dplus/ . dtimes"0 a

echo a dplus/ @ ((dtimes"0)"(1,_)) a
