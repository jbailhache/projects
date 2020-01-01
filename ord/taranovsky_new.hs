module Taranovsky where

 ident x = x

 -- Natural numbers
 data Nat 
  = ZeroN
  | SucN Nat

 -- Ordinals
 data Ord 
  = Zero
  | Suc Ord
  | Lim Ord (Ord -> Ord)

 -- Ordinals
 --data Xord
 -- = Cnt Ord
 -- | Ext (Ord -> Xord)

 -- Ordinal corresponding to a given natural
 ordOfNat ZeroN = Zero
 ordOfNat (SucN n) = Suc (ordOfNat n)

 -- omega
 w = Lim Zero ident 

 lim0 = Lim Zero 

 -- f^n(a)
 iter f Zero a = a
 iter f (Suc b) a = f (iter f b a)
 iter f (Lim k s) a = Lim k (\n -> iter f (s n) a)

 opLim f a = Lim Zero (\n -> f n a)

 opItw f = opLim (iter f)

 -- cardi a = least k with a < W_k
 cardi a = 0 -- todo

 -- a <= b
 le a b = True -- todo

 -- Taranovsky's C(b,a) = generalization of a + w^b
 tc Zero a = Suc a
 tc (Suc b) a = opItw (tc b) a
 tc (Lim k s) a = 
  if le (cardi (Lim k s)) (cardi a)
  then Lim k (\n -> tc (s n) a)
  else opItw (\x -> tc (s x) a) Zero
               
 -- tc (Lim s) a = Lim (\n -> tc (s n) a)
 ---- tc (Ext f) a = Ext (\x -> tc (f x) a)
 -- tc (Ext f z) a = opItw (\x -> tc (f x) a) z 
 ---- tc (Ext f) a = tc (opItw (\x -> f (tc x a)) Zero) a

 --oW = Ext (\x -> x) Zero
 oW = Lim (Suc Zero) ident

 -- epsilon_0 = tc (Ext (\x -> x) Zero) Zero
 epsilon_0 = tc oW Zero

 -- bho = tc (tc (Ext (\x -> x)) (Ext (\x -> x))) Zero
 --bho = tc (Ext (\x -> x) oW) oW

  -- expw a = w^a
 expw a = tc a Zero 


