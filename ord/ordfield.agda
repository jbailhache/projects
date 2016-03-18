module ordfield where

 data Void : Set where
  void : Void 

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

 OrdOfNat : Nat -> Ord
 OrdOfNat O = Zero
 OrdOfNat (1+ n) = Suc (OrdOfNat n)

 omega : Ord
 omega = Lim OrdOfNat

 plus : Ord -> Ord -> Ord
 plus Zero y = y
 plus (Suc x) y = Suc (plus x y)
 plus (Lim f) y = Lim (\(x : Nat) -> plus (f x) y)

 OrdField : Set -> Set
 OrdField s = s -> Ord

 data SetList : Set1 where
  Nil : SetList
  Cons : Set -> SetList -> SetList
 
 First : SetList -> Set
 First Nil = Void
 First (Cons s l) = s

 Rest : SetList -> SetList
 Rest Nil = Nil
 Rest (Cons s l) = l

 data List (sl : SetList) : Set where
  nil : List sl
  cons : First sl -> List (Rest sl) -> List sl

 META : (t : Set) -> (OrdField t -> OrdField t) -> OrdField t -> Ord -> OrdField t
 META t s z Zero = z
 META t s z (Suc x) = s (META t s z x)
 META t s z (Lim phi) = \(x : t) -> Lim (\(n : Nat) -> META t s z (phi n) x)

 a0 : OrdField Void
 a0 _ = omega

 c0 : Ord
 c0 = a0 void

 a1 : OrdField Void -> OrdField Void
 a1 x l = plus omega (x void)

 c1 : Ord
 c1 = a1 a0 void

 b2 : Ord -> (OrdField Void -> OrdField Void) -> OrdField Void -> OrdField Void 
 b2 Zero f y = f y
 b2 (Suc x) f y = META _ (b2 x f) y (y void)
 b2 (Lim phi) f y = \x -> Lim (\(n : Nat) -> b2 (phi n) f y void)

{-
 b2 : Ord -> (Ord -> Ord) -> Ord -> Ord 
 b2 Zero f y = f y
 b2 (Suc x) f y = META Void (b2 x f) y y 
 b2 (Lim phi) f y = Lim (\(n : Nat) -> b2 (phi n) f y)
-}

 a2 : (OrdField Void -> OrdField Void) -> OrdField Void -> OrdField Void
 a2 f x = b2 (x void) f x

 c2 : Ord
 c2 = a2 a1 a0 void

{-
 b3 : Ord -> ((OrdField Void -> OrdField Void) -> OrdField Void -> OrdField Void) -> (OrdField Void -> OrdField Void) -> OrdField Void -> OrdField Void  
 b3 Zero g f y = g f y
 b3 (Suc x) g f y = META _ (b3 x g) f y (y void)
 b3 (Lim phi) g f y = \x -> Lim (\(n : Nat) -> b3 (phi n) g f y void)
-}

 -- b3 : Ord -> ((OrdField Void -> OrdField Void) -> OrdField Void -> OrdField Void) -> (OrdField Void -> OrdField Void) -> OrdField Void -> OrdField Void  
-- b3 : Ord -> ((OrdField _ -> OrdField _) -> OrdField _ -> OrdField _) -> (OrdField _ -> OrdField _) -> OrdField _ -> OrdField _
 b3 : Ord -> ((Ord -> Ord) -> Ord -> Ord) -> (Ord -> Ord) -> Ord -> Ord    
 b3 Zero g f y = g f y
 b3 (Suc x) g f y = META _ (b3 x g) f y y 
 b3 (Lim phi) g f y = Lim (\(n : Nat) -> b3 (phi n) g f y)

 -- a3 :  ((OrdField Void -> OrdField Void) -> OrdField Void -> OrdField Void) -> (OrdField Void -> OrdField Void) -> OrdField Void -> OrdField Void
 a3 : ((Ord -> Ord) -> Ord -> Ord) -> (Ord -> Ord) -> Ord -> Ord
 a3 g f x = b3 x g f x

{-
 b4 : Ord -> (((Ord -> Ord) -> Ord -> Ord) -> (Ord -> Ord) -> Ord -> Ord) -> ((Ord -> Ord) -> Ord -> Ord) -> (Ord -> Ord) -> Ord -> Ord
 b4 Zero h g f y = h g f y
 b4 (Suc x) h g f y = META _ (b4 x h) g f y y
 b4 (Lim phi) h g f y = Lim (\(n : Nat) -> b4 (phi n) h g f y)
-}

 b4 : Ord -> (((OrdField Void -> OrdField Void) -> OrdField Void -> OrdField Void) -> (OrdField Void -> OrdField Void) -> OrdField Void -> OrdField Void) ->  ((OrdField Void -> OrdField Void) -> OrdField Void -> OrdField Void) -> (OrdField Void -> OrdField Void) -> OrdField Void -> OrdField Void
 b4 Zero h g f y = h g f y
 b4 (Suc x) h g f y = META _ (b4 x h) g f y (y void)
 b4 (Lim phi) h g f y = \x -> Lim (\(n : Nat) -> b4 (phi n) h g f y void)

