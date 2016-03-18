module ord where

 data Nat : Set where
  zn : Nat
  sn : Nat -> Nat

 data Ord : Set where
  zo : Ord
  so : Ord -> Ord
  lo : (Nat -> Ord) -> Ord

 ordofnat : Nat -> Ord
  ordofnat zn = zo
  ordofnat (sn n) = so (ordofnat n)

 w : Ord
  w = lo ordofnat

 ford : Nat -> Set
  ford zn = Ord
  ford (sn n) = ford n -> ford n

 lim1 : (Nat -> Ord -> Ord) -> Ord -> Ord
  lim1 f x = lo (\(p : Nat) -> f p x)

 limn : (n : Nat) (Nat -> ford n) -> ford n
  limn zn f = lo f
  limn (sn p) f = \x -> limn p (\q -> f q x)

