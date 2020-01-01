module Ords where

 -- Natural numbers
 data Ord0
  = Zero0
  | Suc0 Ord0

 -- Countable ordinals w1
 data Ord1
  = Zero1
  | Suc1 Ord1
  | Lim01 (Ord0 -> Ord1)

 -- Uncountable ordinals w2
 data Ord2
  = Zero2
  | Suc2 Ord2
  | Lim02 (Ord0 -> Ord2)
  | Lim12 (Ord1 -> Ord2)

 -- Uncountable ordinals w3
 data Ord3
  = Zero3
  | Suc3 Ord3
  | Lim03 (Ord0 -> Ord3)
  | Lim13 (Ord1 -> Ord3)
  | Lim23 (Ord2 -> Ord3)

{-
 -- Ordinals
 data Ord 
  = Zero
  | Suc Ord
  | Lim (Nat -> Ord)
  | Ext (Ord -> Ord)
-}

