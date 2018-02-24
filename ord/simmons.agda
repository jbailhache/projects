module simmons where

 data Nat : Set where
  ZeroN : Nat
  SucN : Nat -> Nat

 data Ord : Set where
  Zero : Ord
  Suc : Ord -> Ord
  Lim : (Nat -> Ord) -> Ord

 OrdOfNat : Nat -> Ord
 OrdOfNat ZeroN = Zero
 OrdOfNat (SucN n) = Suc (OrdOfNat n)

 -- omega
 w = Lim OrdOfNat

 ford : Nat -> Set
 ford ZeroN = Ord
 ford (SucN n) = ford n -> ford n
 
 limn : (n : Nat) -> (Nat -> ford n) -> ford n
 limn ZeroN f = Lim f
 limn (SucN p) f = \x -> limn p (\q -> f q x)

 powern : (n : Nat) -> ((ford n) -> (ford n)) -> Ord -> (ford n) -> (ford n)
 powern n f Zero x = x
 powern n f (Suc a) x = f (powern n f a x)
 powern n f (Lim s) x = limn n (\i -> powern n f (s i) x)

 -- fix f z = least fixed point of f which is > z
 fix : (Ord -> Ord) -> Ord -> Ord
 fix f z = powern ZeroN f w (Suc z) -- Lim (\n -> powern ZeroN f (OrdOfNat n) (Suc z))

 -- cantor b a = a + w^b
 cantor : Ord -> Ord -> Ord
 cantor Zero a = Suc a
 cantor (Suc b) a = fix (cantor b) a
 cantor (Lim s) a = Lim (\n -> cantor (s n) a)
 
 -- expw a = w^a
 expw : Ord -> Ord
 expw a = cantor a Zero

 -- next a = least epsilon_b > a
 next : Ord -> Ord
 next = fix expw

 -- [0]
 simmons0 : ford (SucN (SucN ZeroN))
 simmons0 h = fix (\a -> powern ZeroN h a Zero)

 -- [1]
 simmons1 : ford (SucN (SucN (SucN ZeroN)))
 simmons1 h1 h0 = fix (\a -> powern (SucN ZeroN) h1 a h0 Zero)

 -- [2]
 simmons2 : ford (SucN (SucN (SucN (SucN ZeroN))))
 simmons2 h2 h1 h0 = fix (\a -> powern (SucN (SucN ZeroN)) h2 a h1 h0 Zero)

 simmons3 : ford (SucN (SucN (SucN (SucN (SucN ZeroN)))))
 simmons3 h3 h2 h1 h0 = fix (\a -> powern (SucN (SucN (SucN ZeroN))) h3 a h2 h1 h0 Zero)

 -- Large Veblen ordinal 
 lvo : Ord
 lvo = simmons2 simmons1 simmons0 next w

 -- simmonsn : (n : Nat) -> ford (SucN (SucN n))
 -- simmonsn ZeroN h = fix (\a -> powern ZeroN h a Zero)

 I : {s : Set} -> s -> s
 I x = x

 fnargs : Nat -> (Nat -> Set) -> Set -> Set
 fnargs ZeroN fs t = t
 fnargs (SucN n) fs t = (fs n) -> fnargs n fs t

 insert : {s t u : Set} -> s -> (t -> u) -> (s -> t) -> u
 insert x a f = a (f x)

 tuple : (fs : Nat -> Set) -> (t : Set) -> (u : Set) -> (n : Nat) -> (((fnargs n fs t) -> t) -> u) -> (fnargs n fs u)
 tuple fs t u ZeroN f = f I
 tuple fs t u (SucN n) f = \x -> tuple fs t u n (\y -> f (insert x y))

 -- simmons3b : ford (SucN (SucN (SucN (SucN (SucN ZeroN)))))
 -- simmons3b h3 h2 h1 h0 = fix (\a -> tuple (SucN (SucN (SucN ZeroN))) (\t -> t (powern (SucN (SucN (SucN ZeroN))) h3 a)) h2 h1 h0 Zero)
 --  tuple (SucN (SucN (SucN ZeroN))) (\t -> fix (\a -> t (powern (SucN (SucN (SucN ZeroN))) h a) Zero))

 simmonsn : (n : Nat) -> ford (SucN (SucN n))
 simmonsn n h = tuple (\p -> ford (SucN p)) (ford (SucN ZeroN)) (ford (SucN ZeroN)) n (\t -> fix (\a -> t (powern n h a) Zero))

