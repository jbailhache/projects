module Simmons where

 -- Natural numbers
 data Nat 
  = ZeroN
  | SucN Nat

 -- Ordinals
 data Ord 
  = Zero
  | Suc Ord
  | Lim (Nat -> Ord)

 -- Ordinal corresponding to a given natural
 ordOfNat ZeroN = Zero
 ordOfNat (SucN n) = Suc (ordOfNat n)

 -- omega
 w = Lim ordOfNat

 -- f^a(x)
 fpower f Zero x = x
 fpower f (Suc a) x = f (fpower f a x)
 fpower f (Lim s) x = Lim (\n -> fpower f (s n) x)

 -- fix f z = least fixed point of f which is > z
 fix f z = fpower f w (Suc z) -- Lim (\n -> fpower f (ordOfNat n) (Suc z))

 -- cantor b a = a + w^b
 cantor Zero a = Suc a
 cantor (Suc b) a = fix (cantor b) a
 cantor (Lim s) a = Lim (\n -> cantor (s n) a)
 
 -- expw a = w^a
 expw a = cantor a Zero

 -- next a = least epsilon_b > a
 next = fix expw

 simmons0 h = fix (\a -> fpower h a Zero)

 fpower1 f Zero g x = g x
 fpower1 f (Suc a) g x = f (fpower1 f a g x)
 fpower1 f (Lim s) g x = Lim (\n -> fpower1 f (s n) g x)

 simmons1 h2 h1 = fix (\a -> fpower1 h2 a h1 Zero)
 

