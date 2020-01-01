module Simmons where

 applyto x f = f x 

 data Nat 
  = ZeroN
  | SucN Nat 

 data Ord
  = Zero
  | Suc Ord
  | Lim (Nat -> Ord)

 lim0 f = Lim f

 lims l f x = l (\n -> f n x)

 lim1 = lims lim0
 lim2 = lims lim1
 lim3 = lims lim2

 insert x a f = a (f x)

 ident x = x

 tuple ZeroN f = ident
 tuple (SucN n) f = \x -> tuple n (\a -> f (insert x a))

