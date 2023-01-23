   
load 'math/mt'

dual1 =: 4 : 0
 < (x,0) ,: (y,x)
)

echo 3 5 +/ . * 3 5

a =: (3 dual1 1) , (5 dual1 1)
echo a

dual =: 4 : 0
 < (x * (i. 1+#y) =/ i. 1+#y) + |: (0,y),((#y),1+#y)$0
)


dplus =: (4 : '< (>x) + (>y)')"0 0

dminus =: (4 : '< (>x) - (>y)')"0 0

dopp =: (3 : '< - >y')"0
 
dtimes =: (4 : '< (>x) +/ . * (>y)')"0 0

dinv =: (3 : '< %. >y')"0

ddiv =: (4 : '< (>x) +/ . * %. >y')"0 0

dexp =: (3 : '< geexp_mt_ >y')"0

dsin =: (3 : '< ((geexp_mt_ 0j1 * >y) - (geexp_mt_ - 0j1 * >y)) % 2 * 0j1')"0

dcos =: (3 : '< ((geexp_mt_ 0j1 * >y) + (geexp_mt_ - 0j1 * >y)) % 2')"0


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

m1 =: 4 : 0
 (x * y) - 1 o. y
)

m =: 4 : 0
 (x dtimes y) dminus dsin y
)

echo 'm(2+epsilon,3+zeta)'
echo (2 dual 1 0) m (3 dual 0 1)

value =: 3 : '< y * (i. 3) =/ i. 3'
epsilon =: < 0 0 0, 1 0 0, 0 0 0, 0 0 $ 0
zeta =: < 0 0 0, 0 0 0, 1 0 0, 0 0 $ 0

echo ((value 10) dplus epsilon) g ((value 20) dplus zeta)

eps =: < 0 0 0, 1 0 0, 0 1 0, 0 0 $ 0

h =: 3 : 0
 (y dtimes y dtimes y) dplus ((value 3) dtimes y dtimes y) dplus ((value 5) dtimes y)
)

echo h (value 10) dplus eps

value =: 3 : '< y * (i. 6) =/ i. 6'

epsilon =: 0 0 $ 0
epsilon =: epsilon, 0 0 0 0 0 0
epsilon =: epsilon, 1 0 0 0 0 0
epsilon =: epsilon, 0 0 0 0 0 0
epsilon =: epsilon, 0 1 0 0 0 0
epsilon =: epsilon, 0 0 1 0 0 0
epsilon =: epsilon, 0 0 0 0 0 0
epsilon =: < epsilon

zeta =: 0 0 $ 0
zeta =: zeta, 0 0 0 0 0 0
zeta =: zeta, 0 0 0 0 0 0
zeta =: zeta, 1 0 0 0 0 0
zeta =: zeta, 0 0 0 0 0 0
zeta =: zeta, 0 1 0 0 0 0
zeta =: zeta, 0 0 1 0 0 0
zeta =: < zeta

k1 =: 4 : 0
 (3*x*x) + (5*y*y) + (6*x*y) + (8*x) + (9*y)
)

k =: 4 : 0
 ((value 3) dtimes x dtimes x) dplus ((value 5) dtimes y dtimes y) dplus ((value 6) dtimes x dtimes y) dplus ((value 8) dtimes x) dplus ((value 9) dtimes y)
)

echo ((value 10) dplus epsilon) k ((value 1) dplus zeta)


