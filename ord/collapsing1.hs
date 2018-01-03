module Collapsing where

 -- Natural numbers
 data Nat 
  = ZeroN
  | SucN Nat

 -- Countable ordinals
 data Cord 
  = Zero
  | Suc Cord
  | Lim (Nat -> Cord)

 -- Ordinals
 data Ord
  = Cnt Cord
  | Ext (Cord -> Ord)

 -- Ordinal corresponding to a given natural
 ordOfNat ZeroN = Zero
 ordOfNat (SucN n) = Suc (ordOfNat n)

 -- omega
 w = Lim ordOfNat

 -- plus a b = b + a
 plus Zero b = b
 plus (Suc a) b = Suc (plus a b)
 plus (Lim s) b = Lim (\n -> plus (s n) b)

 iter f ZeroN a = a
 iter f (SucN p) a = iter f p (f a)

 opLim f a = Lim (\n -> f n a)



 o = Ext (\a -> Cnt a)
 o2 = Ext (\a -> Ext (\b -> Cnt (plus a b)))



