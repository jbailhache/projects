module ordmln where

 data Nat : Set where
  O : Nat
  1+ : Nat -> Nat

 data Ord : Set where
  Zero : Ord
  Suc : Ord -> Ord
  Lim : (Nat -> Ord) -> Ord
  
 ford : Nat -> Set
 ford O = Ord
 ford (1+ n) = ford n -> ford n

 NatOfOrd : Nat -> Ord
 NatOfOrd O = Zero
 NatOfOrd (1+ n) = Suc (NatOfOrd n)

 omega : Ord
 omega = Lim NatOfOrd

 plus : Ord -> Ord -> Ord
 plus Zero y = y
 plus (Suc x) y = Suc (plus x y)
 plus (Lim f) y = Lim (\(x : Nat) -> plus (f x) y)

 META0 : (Ord -> Ord) -> Ord -> Ord -> Ord
 META0 s z Zero = z
 META0 s z (Suc x) = s (META0 s z x)
 META0 s z (Lim phi) = Lim (\(x : Nat) -> META0 s z (phi x))

 META1 : (t : Set) -> ((t -> Ord) -> t -> Ord) -> (t -> Ord) -> Ord -> t -> Ord
 META1 t s z Zero = z
 META1 t s z (Suc x) = s (META1 t s z x)
 META1 t s z (Lim phi) = \(x : t) -> Lim (\(n : Nat) -> META1 t s z (phi n) x)

 META2 : (t1 t2 : Set) -> ((t1 -> t2 -> Ord) -> t1 -> t2 -> Ord) -> (t1 -> t2 -> Ord) -> Ord -> t1 -> t2 -> Ord
 META2 t1 t2 s z Zero = z
 META2 t1 t2 s z (Suc x) = s (META2 t1 t2 s z x)
 META2 t1 t2 s z (Lim phi) = \(x1 : t1) -> \(x2 : t2) -> Lim (\(n : Nat) -> META2 t1 t2 s z (phi n) x1 x2)

 data Void : Set where

 data SetList : Set1 where
  Nil : SetList
  Cons : Set -> SetList -> SetList
 
 First : SetList -> Set
 First Nil = Void
 First (Cons s l) = s

 Rest : SetList -> SetList
 Rest Nil = Nil
 Rest (Cons s l) = l

 data ValueOrError (s : Set) : Set where
  Value : s -> ValueOrError s
  Error : ValueOrError s

{-
 data ValueOrErrorSL (s : SetList) : Set where
  Value : s -> ValueOrErrorSL s
  Error : ValueOrErrorSL s
-}

 data List (sl : SetList) : Set where
  nil : List sl
  cons : First sl -> List (Rest sl) -> List sl

 first : (sl : SetList) -> List sl -> ValueOrError (First sl)
 first sl nil = Error
 first sl (cons x l) = Value x

{-
 rest : (sl : SetList) -> List sl -> ValueOrError (Rest sl)
 rest sl nil = Error
 rest sl (cons x l) = Value l
-}

{-
 META : SetList -> ((SetList -> Ord) -> SetList -> Ord) -> (SetList -> Ord) -> Ord -> SetList -> Ord
 META l s z Zero = z
 META l s z (Suc x) = s (META l s z x)
-- META l s z (Lim phi) = \(x1 : t1) -> \(x2 : t2) -> Lim (\(y : Nat) -> META l s z (phi y) x1 x2) 
-- META Nil s z (Lim phi) = \(l : SetList) -> Lim (\(n : Nat) -> META Nil s z (phi n) l)
-- META (Cons t l) s z (Lim phi) = \(x : t) -> META l s z (Lim phi) x
 META l s z (Lim phi) = \(l : SetList) -> Lim (\(n : Nat) -> META l s z (phi n) l) 
-}

 META : (sl : SetList) -> ((List sl -> Ord) -> List sl -> Ord) -> (List sl -> Ord) -> Ord -> List sl -> Ord
 META sl s z Zero = z
 META sl s z (Suc x) = s (META sl s z x)
 META sl s z (Lim phi) = \(l : List sl) -> Lim (\(n : Nat) -> META sl s z (phi n) l) 

-- META2 l s z (Lim phi) = \l -> Lim (\(n : Nat) : META2 l s z (phi n) l)

-- META0 s z x = META Nil s z x Nil
-- META1 t s z x = META (Cons t Nil) s z x t

 a0 : Ord
 a0 = omega

 a'0 : List Nil -> Ord
 a'0 l = omega

 c0 : Ord
 c0 = a0

 a1 : ford (1+ O)
 a1 = plus omega

 a'1 : (List Nil -> Ord) -> List Nil -> Ord
 a'1 x l = plus omega (x nil)

 c1 : Ord 
 c1 = a1 a0
 
-- b2 = Meta
{-
 b2 : (Ord -> Ord) -> Ord -> Ord -> Ord
 b2 f Zero y = f y
 b2 f (Suc x) y = META0 (b2 f x) y y 
 b2 f (Lim phi) y = Lim (\(n : Nat) -> b2 f (phi n) y)
-}

 b2 : Ord -> (Ord -> Ord) -> Ord -> Ord
 b2 Zero f y = f y
 b2 (Suc x) f y = META0 (b2 x f) y y 
 b2 (Lim phi) f y = Lim (\(n : Nat) -> b2 (phi n) f y)

{-
 b'2 : ((SetList -> Ord) -> SetList -> Ord) -> Ord -> (SetList -> Ord) -> SetList -> Ord
 b'2 f Zero y = f y
 b'2 f (Suc x) y = META Nil (b'2 f x) y (y Nil)
 b'2 f (Lim phi) y = \(l : SetList) -> Lim (\(n : Nat) -> b'2 f (phi n) y l)
-}

{-
 b'2 : Ord -> ((SetList -> Ord) -> SetList -> Ord) -> (SetList -> Ord) -> SetList -> Ord
 b'2 Zero f y = f y
 b'2 (Suc x) f y = META Nil (b'2 x f) y (y Nil)
 b'2 (Lim phi) f y = \(l : SetList) -> Lim (\(n : Nat) -> b'2 (phi n) f y l)
-}

-- b'2 : Ord -> (Ord -> Ord) -> Ord -> Ord
 b'2 : Ord -> ((List Nil -> Ord) -> List Nil -> Ord) -> (List Nil -> Ord) -> List Nil -> Ord
 b'2 Zero f y = f y
 b'2 (Suc x) f y = META Nil (b'2 x f) y (y nil)
 b'2 (Lim phi) f y = \(l : List Nil) -> Lim (\(n : Nat) -> b'2 (phi n) f y nil)

 a2 : ford (1+ (1+ O))
-- a2 f x = b2 f x x
 a2 f x = b2 x f x

{-
-- a'2 : (Ord -> Ord) -> Ord -> Ord
 a'2 : ((SetList -> Ord) -> SetList -> Ord) -> Ord -> SetList -> Ord
-- a'2 f x = b'2 f x ((l : SetList) -> x)
 a'2 f x = b'2 x f (\(l : SetList) -> x)
-}

 a'2 : ((List Nil -> Ord) -> List Nil -> Ord) -> (List Nil -> Ord) -> List Nil -> Ord
 a'2 f x = b'2 (x nil) f x

 c2 : Ord 
 c2 = a2 a1 a0

-- c'2 : Ord
-- c'2 = a'2 a1 a0

 c'2 : Ord
 c'2 = a'2 a'1 a'0 nil
 
-- b3 = metan
{-
 b3 : ((Ord -> Ord) -> Ord -> Ord) -> Ord -> (Ord -> Ord) -> Ord -> Ord
 b3 m Zero f y = m f y
 b3 m (Suc x) f y = META1 _ (b3 m x) f y y
 b3 m (Lim phi) f y = Lim (\(n : Nat) -> b3 m (phi n) f y)
-}

 b3 : Ord -> ((Ord -> Ord) -> Ord -> Ord) -> (Ord -> Ord) -> Ord -> Ord
 b3 Zero g f y = g f y
 b3 (Suc x) g f y = META1 _ (b3 x g) f y y
 b3 (Lim phi) g f y = Lim (\(n : Nat) -> b3 (phi n) g f y)

{-
 b'3 : (((SetList -> Ord) -> SetList -> Ord) -> (SetList -> Ord) -> SetList -> Ord) -> Ord -> ((SetList -> Ord) -> SetList -> Ord) -> (SetList -> Ord) -> SetList -> Ord
 b'3 m Zero f y = m f y
-- b'3 m (Suc x) f y = META (Cons _ Nil) (b'3 m x) f y (y Nil)
 b'3 m (Suc x) f y = META (Cons _ Nil) f y (y Nil)
 b'3 m (Lim phi) f y = \(l : SetList) -> Lim (\(n : Nat) -> b'3 m (phi n) f y l)
-}

{-
 b'3 : Ord -> (((SetList -> Ord) -> SetList -> Ord) -> (SetList -> Ord) -> SetList -> Ord) -> ((SetList -> Ord) -> SetList -> Ord) -> (SetList -> Ord) -> SetList -> Ord
 b'3 Zero g f y = g f y
 b'3 (Suc x) g f y = META (Cons _ Nil) (b'3 x g) f y (y Nil)
-- b'3 (Suc x) g f y = META (Cons _ Nil) f y (y Nil)
 b'3 (Lim phi) g f y = \(l : SetList) -> Lim (\(n : Nat) -> b'3 (phi n) g f y l)
-}

{-
 b'2 : Ord -> ((List Nil -> Ord) -> List Nil -> Ord) -> (List Nil -> Ord) -> List Nil -> Ord
 b'2 Zero f y = f y
 b'2 (Suc x) f y = META Nil (b'2 x f) y (y nil)
 b'2 (Lim phi) f y = \(l : List Nil) -> Lim (\(n : Nat) -> b'2 (phi n) f y nil)
-}

{-
 b'3 : (t : Set) -> Ord -> (((List (Cons t Nil) -> Ord) -> List (Cons t Nil) -> Ord) -> (List (Cons t Nil) -> Ord) -> List (Cons t Nil) -> Ord) -> ((List (Cons t Nil) -> Ord) -> List (Cons t Nil) -> Ord) -> (List (Cons t Nil) -> Ord) -> List (Cons t Nil) -> Ord
 b'3 t Zero g f y = g f y
 b'3 t (Suc x) g f y = META (Cons t Nil) (b'3 t x g) f y (y nil)
 b'3 t (Lim phi) g f y = Lim (\(n : Nat) -> b'3 t (phi n) g f y nil)
-}

{-
 probleme :
  b'3 t x g est de type :
   ((List (Cons t Nil) -> Ord) -> List (Cons t Nil) -> Ord) -> (List (Cons t Nil) -> Ord) -> List (Cons t Nil) -> Ord
  or le 2eme argument de META doit etre de type :
    (List sl -> Ord) -> List sl -> Ord
  avec sl = Cons t Nil donc
    (List (Cons t Nil) -> Ord) -> List (Cons t Nil) -> Ord
  avec t = Ord ce type est equivalent a :
    (Ord -> Ord) -> Ord -> Ord 
-}

 b'3 : (t : Set) -> Ord -> (((List (Cons t Nil) -> Ord) -> List (Cons t Nil) -> Ord) -> (List (Cons t Nil) -> Ord) -> List (Cons t Nil) -> Ord) -> ((List (Cons t Nil) -> Ord) -> List (Cons t Nil) -> Ord) -> (List (Cons t Nil) -> Ord) -> List (Cons t Nil) -> Ord
 b'3 t Zero g f y = g f y
 b'3 t (Suc x) g f y = META (Cons t Nil) (b'3 t x g f) y (y nil) 
 b'3 t (Lim phi) g f y = \(l : List (Cons t Nil)) -> Lim (\(n : Nat) -> b'3 t (phi n) g f y nil)

 a3 : ford (1+ (1+ (1+ O)))
-- a3 y3 f x = b3 y3 x f x
-- a3 y3 f x = b3 x y3 f x
 a3 g f x = b3 x g f x

-- a'3 : (((SetList -> Ord) -> SetList -> Ord) -> Ord -> SetList -> Ord) ->  ((SetList -> Ord) -> SetList -> Ord) -> Ord -> SetList -> Ord
-- a'3 y3 f x = b'3 y3 x f (\(l : SetList) -> x)
 
-- a'3 g f x = b'3 x g f ((l : SetList) -> x)
 
-- b4 = primn
 b4 : {t : Set} -> ((t -> Ord -> Ord) -> t -> Ord -> Ord) -> Ord -> (t -> Ord -> Ord) -> t -> Ord -> Ord
 b4 p Zero m f x = p m f x
 b4 p (Suc n) m f x = META2 _ _ (b4 p n) m x f x
 b4 p (Lim phi) m f x = Lim (\(y : Nat) -> b4 p (phi y) m f x)

 a4 : ford (1+ (1+ (1+ (1+ O))))
 a4 y4 y3 f x = b4 y4 x y3 f x

