   
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
 
dtimes =: 4 : 0
 < (>x) +/ . * (>y)
)

echo dplus/ a dtimes"0 a

echo a dplus/ . dtimes"0 a

echo a dplus/ @ ((dtimes"0)"(1,_)) a
