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

 --chainnest x a 0 = x
 --chainnest x a (b+1) = Chain a (Nest (chainnest x a b))

 --nestchain x a 0 = x
 --nestchain x a (b+1) = Nest (Chain a (nestchain x a b))

 --f a b = xop (chainnest Add a b) a a

 add a b = a + b

 chain 0 x a b = x a b
 chain (n+1) x a 1 = a
 chain (n+1) x a (b+1) = chain n x a (chain (n+1) x a b)

 nest x a 1 = a
 nest x a (b+1) = chain (nest x a b) x a a

 chainnest x a 0 = x
 chainnest x a (b+1) = chain a (nest (chainnest x a b))

 nestchain x a 0 = x
 nestchain x a (b+1) = nest (chain a (nestchain x a b))

 f a b = chainnest add a b a a
 g a b = nestchain add a b a a

-- Correspondence with Bower's array / extended operator notation
-- {a,b,c,d,e} = a {c,d,e} b with {c,d,e} = chain (c-1) $ nest $ chain (d-1) $ nest $ chain (e-1) add

