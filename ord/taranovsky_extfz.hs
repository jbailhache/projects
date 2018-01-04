module Taranovsky where

 -- Natural numbers
 data Nat 
  = ZeroN
  | SucN Nat

 -- Ordinals
 data Ord 
  = Zero
  | Suc Ord
  | Lim (Nat -> Ord)
  | Ext (Ord -> Ord) Ord

 -- Ordinals
 --data Xord
 -- = Cnt Ord
 -- | Ext (Ord -> Xord)

 -- Ordinal corresponding to a given natural
 ordOfNat ZeroN = Zero
 ordOfNat (SucN n) = Suc (ordOfNat n)

 -- omega
 w = Lim ordOfNat

 lim0 s = Lim s

 iter f ZeroN a = a
 iter f (SucN p) a = iter f p (f a)

 opLim f a = Lim (\n -> f n a)

 opItw f = opLim (iter f)

 -- Taranovsky's C(b,a) = generalization of a + w^b
 tc Zero a = Suc a
 tc (Suc b) a = opItw (tc b) a
 tc (Lim s) a = Lim (\n -> tc (s n) a)
 -- tc (Ext f) a = Ext (\x -> tc (f x) a)
 tc (Ext f z) a = opItw (\x -> tc (f x) a) z 
 -- tc (Ext f) a = tc (opItw (\x -> f (tc x a)) Zero) a

 oW = Ext (\x -> x) Zero

 -- epsilon_0 = tc (Ext (\x -> x) Zero) Zero
 epsilon_0 = tc oW Zero

 -- bho = tc (tc (Ext (\x -> x)) (Ext (\x -> x))) Zero
 bho = tc (Ext (\x -> x) oW) oW

  -- expw a = w^a
 expw a = tc a Zero 


