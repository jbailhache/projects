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

 lim0 s = Lim s
 lim1 f x = lim0 (\n -> f n x)
 lim2 f x = lim1 (\n -> f n x)

 -- f^a(x)
 fpower0 f Zero x = x
 fpower0 f (Suc a) x = f (fpower0 f a x)
 fpower0 f (Lim s) x = Lim (\n -> fpower0 f (s n) x)

 fpower l f Zero x = x
 fpower l f (Suc a) x = f (fpower l f a x)
 fpower l f (Lim s) x = l (\n -> fpower l f (s n) x)

 -- fix f z = least fixed point of f which is > z
 fix f z = fpower0 f w (Suc z) -- Lim (\n -> fpower0 f (ordOfNat n) (Suc z))

 -- cantor b a = a + w^b
 cantor Zero a = Suc a
 cantor (Suc b) a = fix (cantor b) a
 cantor (Lim s) a = Lim (\n -> cantor (s n) a)
 
 -- expw a = w^a
 expw a = cantor a Zero

 -- next a = least epsilon_b > a
 next = fix expw

 -- [0]
 simmons0 h = fix (\a -> fpower0 h a Zero)

 fpower1 f1 Zero f0 x = f0 x
 fpower1 f1 (Suc a) f0 x = f1 (fpower1 f1 a f0) x
 fpower1 f1 (Lim s) f0 x = Lim (\n -> fpower1 f1 (s n) f0 x)

{- or :
 fpower1 f1 Zero f0 = f0 
 fpower1 f1 (Suc a) f0 = f1 (fpower1 f1 a f0) 
 fpower1 f1 (Lim s) f0 = \x -> Lim (\n -> fpower1 f1 (s n) f0 x)

 or :

 fpower1 f1 Zero f0 = f0 
 fpower1 f1 (Suc a) f0 = f1 (fpower1 f1 a f0) 
 fpower1 f1 (Lim s) f0 = lim1 (\n -> fpower1 f1 (s n) f0)
-}

 -- [1]
 simmons1 h1 h0 = fix (\a -> fpower1 h1 a h0 Zero)

 fpower2 f2 Zero f1 f0 x = f1 f0 x
 fpower2 f2 (Suc a) f1 f0 x = f2 (fpower2 f2 a f1) f0 x
 fpower2 f2 (Lim s) f1 f0 x = Lim (\n -> fpower2 f2 (s n) f1 f0 x)

 -- [2]
 simmons2 h2 h1 h0 = fix (\a -> fpower2 h2 a h1 h0 Zero)
 
 -- Large Veblen ordinal 
 lvo = simmons2 simmons1 simmons0 next w

