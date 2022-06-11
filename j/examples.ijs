
sqrt =: ^ & 0.5
echo sqrt(2)
echo sqrt(sqrt(2))
echo sqrt^:2(2)
echo sqrt^:_1(2)

echo + / i. 11
echo (i. 11) + / i. 11
echo + / ~ i. 11

suc =: + & 1
double =: * & 2
echo (double @ suc) 5
echo (double @: suc) 5

to =: - ~
echo 10 to 16

transpose =: |:
matprod =: + / . *
A =: 2 2 $ 1 2 3 4
echo A
echo transpose A
echo A matprod A
B =: 2 2 2 $ 1 2 3 4 5 6 7 8
echo B
echo B matprod A

t =: 10 # 1 20 $ 20 # '.'
echo ('X' 5 } 3 { t) 3 } t


[ a234 =: i. 2 3 4
[ a45 =: i. 4 5
[ a56 =: i. 5 6
a2345 =: i. 2 3 4 5
$ a2345

$ |: a2345  NB. transpose
$ 1 0 2 3 |: a2345

$ a234 */ a56  NB. external product

$ a234 +/ .* a45  NB. tensorial product

[ a66 =: i. 6 6 
[ i6 =: = / ~ i. # a66  NB. identity
[ d6 =: a66 * i6        NB. diagonal matrix
NB. o6 =: (# a66) # 1     NB. vector of ones
NB. o6
NB. v6 =: d6 +/ .* o6     NB. diagonal vector
[ v6 =: +/ d6           NB. diagonal vector
+/ v6                 NB. trace
+/ +/ d6

, i6
, a66
(, i6) +/ . * , a66  NB. Another way of computing trace

[ a55 =: i. 5 5
[ i55 =: = / ~ i. # a55
[ i355 =: (3 # 1) */ i55
[ a355 =: i. 3 5 5
[ d355 =: i355 * a355
[ d553 =: |: d355
[ t =: +/ +/ d553

a553 =: |: a355
i553 =: i55 */ 3 # 1
d553b =: i553 * a553
[ tb =: +/ +/ d553b

(,. a355) +/ . * , i55 

a3455 =: i. 3 4 5 5
(3 4 25 $ , a3455) +/ . * , i55

a5534 =: i. 5 5 3 4
(, i55) +/ . * 25 3 4 $ , a5534


5 -~ 8  NB. swap operands

a =: 'b'
(a) =: 123
b

i. 10
+/ i. 10  NB. sum of array 
+/ \ i. 10  NB. cumul
+/ 10 20 30 40  NB. sum
# 10 20 30 40  NB. number
(+/ % #) 10 20 30 40  NB. average is sum divided by number
avg =: +/ % #
avg 10 20 30 40

a45
+/ a45  NB. sum of rows or sum of elements of each column
+/"1 a45  NB. sum of columns or sum of elements of each row

a234       NB. three dimensional array with 2 sheets, 3 rows and 4 colums
+/ a234    NB. sum of sheets
+/"3 a234  NB. sum of sheets
+/"2 a234  NB. sum of rows
+/"1 a234  NB. sum of columns

([: i. */) 3 4 5

1 2 3 ; 4 5 ; 6 7 8
1 { 1 2 3 ; 4 5 ; 6 7 8
(* & 10) &> < 1 2 3
(* & 10) &.> < 1 2 3

(* & 2) 10  NB. double
((* & 2) ^: 8) 10  NB. function power

abs =: + ` - @. (< & 0)  NB. absolute value
abs 5
abs _6

NB. Shadow Hunter attack
1 + i. 6  NB. die with 6 sides
1 + i. 4  NB. die with 4 sides
| (1 + i. 6) -/ (1 + i. 4)  NB. difference
+/ +/ (| (1 + i. 6) -/ (1 + i. 4)) =/ i. 6  NB. number of occurences of each difference


