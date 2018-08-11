module Simmons where

 applyto x f = f x 

 data Nat 
  = ZeroN
  | SucN Nat 

 data Ord
  = Zero
  | Suc Ord
  | Lim (Nat -> Ord)

 -- Ordinal corresponding to a given natural
 ordOfNat ZeroN = Zero
 ordOfNat (SucN n) = Suc (ordOfNat n)

 -- omega
 w = Lim ordOfNat

 lim0 f = Lim f

 lims l f x = l (\n -> f n x)

 lim1 = lims lim0
 lim2 = lims lim1
 lim3 = lims lim2

 -- limn ZeroN = lim0
 -- limn (SucN n) = lims (limn n)

 insert x a f = a (f x)

 ident x = x

 -- tuple ZeroN f = ident
 -- tuple (SucN n) f = \x -> tuple n (\a -> f (insert x a))

 fpower l Zero f x = x
 fpower l (Suc a) f x = f (fpower l a f x)
 fpower l (Lim s) f x = l (\n -> fpower l (s n) f x)

 -- fix f z = least fixed point of f which is > z
 fix f z = fpower lim0 w f (Suc z) 

 -- [0]
 s0 h = fix (\a -> fpower lim0 a h Zero)

 -- [1]
 s1 h1 h0 = fix (\a -> fpower lim1 a h1 h0 Zero)

 -- [2]
 s2 h2 h1 h0 = fix (\a -> fpower lim2 a h2 h1 h0 Zero)

 tpower l a h gs x = gs (fpower l a h) x
 
