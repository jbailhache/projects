module Main where

 add a b = a + b

 rep f 0 x = x
 rep f (n+1) x = f (rep f n x)

 increase n op a 0 = a
 increase 0 op a (b+1) = op a (increase 0 op a b)
 increase (n+1) op a (b+1) = increase n (rep (increase n) (increase (n+1) op a b) op) a a

