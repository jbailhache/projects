module Main where

 op 0 a b = a + b
 op (n+1) a 0 = a
 op (n+1) a (b+1) = op n a (op (n+1) a b) 

 data Xop = Add | Ext Integer Xop

 xop Add a b = a + b
 xop (Ext 0 x) a b = xop x a b
 xop (Ext (n+1) x) a 0 = a
 xop (Ext (n+1) x) a (b+1) = xop (Ext n x) a (xop (Ext (n+1) x) a b)

