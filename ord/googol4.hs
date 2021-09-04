module Main where

 op 1 a b = a + b
 op (n+1) a 1 = a
 op (n+1) a (b+1) = op n a (op (n+1) a b) 

 data Xop = Add | Chain Integer Xop | Nest Xop

 xop Add a b = a + b
 xop (Chain 0 x) a b = xop x a b
 xop (Chain (n+1) x) a 1 = a
 xop (Chain (n+1) x) a (b+1) = xop (Chain n x) a (xop (Chain (n+1) x) a b)
 xop (Nest x) a 1 = a
 xop (Nest x) a (b+1) = xop (Chain (xop (Nest x) a b) x) a a
 