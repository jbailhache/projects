module Main where

 op 0 a b = a + b
 op (n+1) a 0 = a
 op (n+1) a (b+1) = op n a (op (n+1) a b) 

