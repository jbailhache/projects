module Cord_and_ord where

 -- Natural numbers
 data Nat 
  = ZeroN
  | SucN Nat

 -- Countable ordinals
 data Cord
  = ZeroC
  | SucC Cord
  | LimC (Nat -> Cord)

 -- Ordinals
 data Ord 
  = Zero
  | Suc Ord
  | Lim (Nat -> Ord)
  | Ext (Ord -> Ord)

 ordOfCord ZeroC = Zero
 ordOfCord (SucC a) = Suc (ordOfCord a)
 ordOfCord (LimC s) = Lim (\n -> ordOfCord (s n))

 cordOfOrd Zero = ZeroC
 cordOfOrd (Suc a) = SucC (cordOfOrd a)
 cordOfOrd (Lim s) = LimC (\n -> cordOfOrd (s n))
 cordOfOrd (Ext f) = cordOfOrd (f Zero)

