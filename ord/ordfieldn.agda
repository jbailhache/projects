module ordfieldn where

 data Void : Set where
  void : Void

 data Nat : Set where
  O : Nat
  1+ : Nat -> Nat

 data OrdField (t : Set) : Set where
  Zero : OrdField t
  Suc : OrdField t -> OrdField t
  Lim : (Nat -> OrdField t) -> OrdField t
  Fnc : (t -> OrdField Void) -> OrdField t
--  Fnc : (t -> OrdField t) -> OrdField t

{-
 convert : (t : Set) -> (u : Set) -> (c : u -> t) -> OrdField t -> OrdField u
 convert t u c Zero = Zero
 convert t u c (Suc x) = Suc (convert t u c x)
 convert t u c (Lim f) = Lim (\(n : Nat) -> convert t u c (f n))
 convert t u c (Fnc f) = Fnc (\(a : u) -> convert t u c (f (c a)))
-}

 Ord : Set
 Ord = OrdField Void

 apply : (t : Set) -> OrdField t -> (a : t) -> OrdField Void
-- apply : (t : Set) -> OrdField t -> (a : t) -> OrdField t
 apply t Zero a = Zero
 apply t (Suc x) a = Suc (apply t x a)
 apply t (Lim f) a = Lim (\(n : Nat) -> apply t (f n) a)
 apply t (Fnc f) a = f a

 OrdFnc : Set -> Nat -> Set
 OrdFnc t O = OrdField t
 OrdFnc t (1+ n) = OrdFnc t n -> OrdFnc t n

 OrdOfNat : Nat -> OrdField Void
 OrdOfNat O = Zero
 OrdOfNat (1+ n) = Suc (OrdOfNat n)

 omega : Ord
 omega = Lim OrdOfNat

 plus : (t : Set) -> OrdField t -> OrdField t -> OrdField t
 plus t Zero y = y
 plus t (Suc x) y = Suc (plus t x y)
 plus t (Lim f) y = Lim (\(n : Nat) -> plus t (f n) y)
-- plus t (Fnc f) y = Fnc (\(a : t) -> plus t (Fnc (\(b : t) -> apply _ (f a) void)) y)
 plus t (Fnc f) y = Fnc (\(a : t) -> plus Void (f a) (apply t y a))
-- plus t (Fnc f) y = Fnc (\(a : t) -> plus t (f a) y)

 META : (t : Set) -> (OrdField t -> OrdField t) -> OrdField t -> OrdField Void -> OrdField t
-- META : (t : Set) -> (OrdField t -> OrdField t) -> OrdField t -> OrdField t -> OrdField t
-- META : (t : Set) -> (OrdField (OrdField t) -> OrdField (OrdField t)) -> OrdField (OrdField t) -> OrdField t -> OrdField t
 META t s z Zero = z
 META t s z (Suc x) = s (META t s z x)
 META t s z (Lim f) = Fnc (\(x : t) -> Lim (\(n : Nat) -> apply t (META t s z (f n)) x))
-- META t s z (Fnc f) = Fnc (\(a : t) -> META t s z (f a))
 META t s z (Fnc f) = Zero
-- META t s z (Fnc f) = Fnc (\(a : t) -> META t s z (f a))

 a0 : Ord
 a0 = omega
 
 c0 : Ord
 c0 = a0

 a1 : Ord -> Ord
 a1 x = plus Void omega x

 c1 : Ord 
 c1 = a1 a0

-- b2 : OrdField Void -> (OrdField Void -> OrdField Void) -> OrdField Void -> OrdField Void
 b2 : Ord -> OrdFnc Void (1+ (1+ O))
 b2 Zero f y = f y
 b2 (Suc x) f y = META Void (b2 x f) y y
 b2 (Lim phi) f y = Lim (\(n : Nat) -> b2 (phi n) f y)
 b2 (Fnc phi) f y = Fnc (\(a : Void) -> b2 (phi a) f y)
 
 a2 : (Ord -> Ord) -> Ord -> Ord
 a2 f x = b2 x f x

 c2 : Ord
 c2 = a2 a1 a0

 b3 : OrdField Void -> OrdFnc Void (1+ (1+ (1+ O)))
 b3 Zero g f y = g f y
-- b3 (Suc x) g f y = META Ord (b3 x g) f y y
-- b3 (Suc x) g f y = META Ord (\(f' : OrdField Ord) -> Fnc (b3 x g (\(x : Ord) -> apply Ord f' x))) f y y
 b3 (Suc x) g f y = apply _ (META Ord (\(f' : OrdField Ord) -> Fnc (b3 x g (\(x : Ord) -> apply Ord f' x))) (Fnc f) y) y
-- b3 (Suc x) g f y = convert Ord Void (\z -> Zero) (META Ord (\f' -> apply _ (Fnc (\x -> convert Void Ord (\z -> void) (b3 x g (\x' -> convert Ord Void (\v -> Zero) (apply Ord f' x')) x))) (convert Ord Void (\z -> Zero) f')) (convert Void Ord (\z -> void) y) (convert Void Ord (\z -> void) y))
 b3 (Lim phi) g f y = Lim (\(n : Nat) -> b3 (phi n) g f y)
 b3 (Fnc phi) g f y = Fnc (\(a : Void) -> b3 (phi a) g f y)

{-
 b3 : OrdField Ord -> OrdFnc Ord (1+ (1+ O))
 b3 Zero g f = Fnc (apply _ (g f))
-- b3 (Suc x) g f = Fnc (\y -> apply (OrdField Ord) (apply (OrdField Ord) (META Ord (b3 x g) f) y) y)
 b3 (Suc x) g f = Fnc (\y -> META Ord (\f' -> Fnc (b3 x g (apply Ord f'))) f y y)
 b3 (Lim phi) g f = Fnc (\y -> Lim (\(n : Nat) -> apply _ (b3 (phi n) g f) y))
 b3 (Fnc phi) g f = Fnc (\y -> Fnc (\(a : Ord) -> apply _ (b3 (phi a) g f) y))
-}

 a3 : ((Ord -> Ord) -> Ord -> Ord) -> (Ord -> Ord) -> Ord -> Ord
 a3 g f x = b3 x g f x

 c3 : Ord
 c3 = a3 a2 a1 a0

 b4 : OrdField Void -> OrdFnc Void (1+ (1+ (1+ (1+ O))))
 b4 Zero h g f y = h g f y
-- b4 (Suc x) h g f y = META (OrdField Ord) (b4 h x) g f y y
 b4 (Suc x) h g f y = apply _ (META Ord (\(g' : OrdField Ord) -> Fnc (b3 x h (\(x : Ord) -> apply Ord g' x))) (Fnc g) f y) y
 b4 (Lim phi) h g f y = Lim (\(n : Nat) -> b4 (phi n) h g f y)
 b4 (Fnc phi) h g f y = Fnc (\(a : Void) -> b4 (phi a) h g f y)

  
  
