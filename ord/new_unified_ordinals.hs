module Ords where

 -- Ordinals
 data Ord 
  = Zero
  | One
  | W Ord
  | Sup Ord (Ord -> Ord)

 two = Sup One (\x -> One)
 three = Sup One (\x -> two)

 suc a = Sup One (\x -> a)

 -- f^a(x)
 fpower0 f Zero x = x
 -- fpower0 f (Suc a) x = f (fpower0 f a x)
 fpower0 f (Sup One s) x = f (fpower0 f (s Zero) x)
 -- fpower0 f (Lim s) x = Lim (\n -> fpower0 f (s n) x)
 -- fpower0 f (Sup W0 s) x = Sup W0 (\n -> fpower0 f (s n) x) 

 w_times_2 = Sup (W Zero) (\n -> fpower0 suc n (W Zero))

