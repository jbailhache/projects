module ordrep where

-- Primitive data types

 data Bool : Set where
  true : Bool
  false : Bool

 {-# BUILTIN BOOL Bool #-}
 {-# BUILTIN TRUE true #-}
 {-# BUILTIN FALSE false #-}

 if_then_else_ : {A : Set} -> Bool -> A -> A -> A
 if true then x else y = x
 if false then x else y = y

 _and_ : Bool -> Bool -> Bool
 true and x = x
 false and x = false

 _or_ : Bool -> Bool -> Bool
 true or x = true
 false or x = x

 data Nat : Set where
  O : Nat
  1+ : Nat -> Nat

 {-# BUILTIN NATURAL Nat #-}
 {-# BUILTIN ZERO    O #-}
 {-# BUILTIN SUC     1+ #-}

 _+_ : Nat -> Nat -> Nat
 O + n = n
 1+ n + p = 1+ (n + p)

 _-_ : Nat -> Nat -> Nat
 n - O = n
 O - n = O
 (1+ n) - (1+ p) = n - p

 _==_ : Nat -> Nat -> Bool
 O == O = true
 (1+ n) == O = false
 O == (1+ n) = false
 1+ n == 1+ p = n == p
 
 _>=_ : Nat -> Nat -> Bool
 O >= O = true
 O >= 1+ n = false
 1+ n >= O = true
 1+ n >= 1+ p = if n >= p then true else false
 
 postulate
  String : Set

 {-# BUILTIN STRING String #-}

 private
  primitive
   primStringEquality : String -> String -> Bool
   primStringAppend : String -> String -> String 

 infixr 5 _cat_

 _eq_ : String → String → Bool
 _eq_ = primStringEquality

 _cat_ : String -> String -> String
 _cat_ = primStringAppend


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

 
-- SLC terms are proofs

 data Proof : Set where
  AXM : Proof
  SMB : String -> Proof
  DB0 : Proof
  DBS : Proof -> Proof
  DBL : Proof -> Proof
  APL : Proof -> Proof -> Proof
  LTR : Proof -> Proof -> Proof

-- Syntactic equality of proofs
 _===_ : Proof -> Proof -> Bool
 SMB s === SMB t = s eq t 
 DB0 === DB0 = true
 DBS x === DBS y = x === y
 DBL x === DBL y = x === y
 APL x y === APL x' y' = (x === x') and (y === y')
 LTR x y === LTR x' y' = (x === x') and (y === y')
 AXM === AXM = true
 x === y = false

 shift : Proof -> Proof -> Proof
 shift u AXM = AXM
 shift u (SMB s) = SMB s
 shift u DB0 = DB0
 shift u (DBS x) = if u === DBS x then DBS u else DBS (shift u x)
 shift u (DBL x) = DBL (shift (DBS u) x)
 shift u (APL x y) = APL (shift u x) (shift u y)
 shift u (LTR x y) = LTR (shift u x) (shift u y)

-- variable substitution
 subst : Proof -> Proof -> Proof -> Proof
 subst1 : Proof -> Proof -> Proof -> Proof
 subst u a b = if u === a then b else (if DBS u === a then u else subst1 u a b)
 subst1 u AXM b = AXM
 subst1 u (SMB s) b = (SMB s)
 subst1 u DB0 b = DB0
 subst1 u (DBL x) b = DBL (subst (DBS u) x (shift DB0 b))
 subst1 u (DBS x) b = DBS (subst u x b)
 subst1 u (APL x y) b = APL (subst u x b) (subst u y b)
 subst1 u (LTR x y) b = LTR (subst u x b) (subst u y b)

 red1 : Proof -> Proof
 red1 AXM = AXM
 red1 (SMB s) = (SMB s)
 red1 DB0 = DB0
 red1 (DBS x) = DBS x
 red1 (DBL x) = DBL (red1 x)
 red1 (APL (DBL x) y) = subst (DB0) x y
 red1 (APL x y) = APL (red1 x) (red1 y)
 red1 (LTR x y) = LTR (red1 x) (red1 y)

 redn : Nat -> Proof -> Proof
 redn O x = x
 redn (1+ n) x = if (red1 x) === x then x else redn n (red1 x)

 red : Proof -> Proof
 red a = redn 10000 a
 
 side : Proof -> Bool -> Proof -> Proof
 side t s AXM = if s then (APL t (DBL (DBL (DBS DB0)))) else (APL t (DBL (DBL DB0)))
 side _ _ (SMB s) = (SMB s)
 side _ _ DB0 = DB0
 side _ _ (DBS x) = DBS x
 side t s (DBL x) = DBL (side t s x)
 side t s (APL x y) = APL (side t s x) (side t s y)
 side t s (LTR x y) = if red (side t true x) === red (side t true y) then (if s then red (side t false x) else red (side t false y)) else (LTR x y)

-- does a proof contain a symbol ?
 _contSym_ : Proof -> String -> Bool
 AXM contSym _ = false
 SMB s contSym s' = s eq s'
 DB0 contSym _ = false
 (DBS x) contSym s = x contSym s 
 (DBL x) contSym s = x contSym s
 (APL x y) contSym s = (x contSym s) or (y contSym s)
 (LTR x y) contSym s = (x contSym s) or (y contSym s)

-- abstraction
 abstr : Proof -> String -> Proof -> Proof
 abst : Proof -> String -> Proof -> Proof
 abst n s x = if x contSym s then abstr n s x else x
 abstr n s AXM = AXM
 abstr n s (SMB x) = if s eq x then n else SMB x
 abstr n s DB0 = DB0
 abstr n s (DBS x) = DBS (abst n s x)
 abstr n s (DBL x) = DBL (abst (DBS n) s x)
 abstr n s (APL x y) = APL (abst n s x) (abst n s y)
 abstr n s (LTR x y) = LTR (abst n s x) (abst n s y)

 lambda : String -> Proof -> Proof
 lambda s x = DBL (abst DB0 s x)

{-
 representation of ordinals with proofs
 symbols : Zero, Suc, H 
 H f x = lim \n. f**n(x)
-}

 repeat : Nat -> Proof -> Proof -> Proof
 repeat O f x = x
 repeat (1+ n) f x = APL f (repeat n f x)

 nth : Nat -> Proof -> Proof
 nthAPL : Nat -> Proof -> Proof -> Proof
 nthAPL2 : Nat -> Proof -> Proof -> Proof -> Proof
 nth n AXM = AXM
 nth n (SMB s) = SMB s
 nth n DB0 = DB0
 nth n (DBS x) = DBS x
 nth n (DBL x) = DBL (nth n x)
 nth n (LTR x y) = LTR (nth n x) (nth n y)
 nth n (APL x y) = nthAPL n x y
 nthAPL n AXM y = APL AXM (nth n y)
 nthAPL n (SMB s) y = APL (SMB s) (nth n y)
 nthAPL n DB0 y = APL DB0 (nth n y)
 nthAPL n (DBS x) y = APL (DBS x) (nth n y)
 nthAPL n (DBL x) y = APL (DBL (nth n x)) (nth n y)
 nthAPL n (LTR x1 x2) y = APL (LTR (nth n x1) (nth n x2)) (nth n y)
 nthAPL n (APL x1 x2) y = nthAPL2 n x1 x2 y 
 nthAPL2 n AXM y z = APL (APL AXM (nth n y)) (nth n z)
 nthAPL2 n DB0 y z = APL (APL DB0 (nth n y)) (nth n z)
 nthAPL2 n (DBS x) y z = APL (APL (DBS x) (nth n y)) (nth n z)
 nthAPL2 n (DBL x) y z = APL (APL (DBL (nth n x)) (nth n y)) (nth n z)
 nthAPL2 n (LTR x1 x2) y z = APL (APL (LTR (nth n x1) (nth n x2)) (nth n y)) (nth n z)
 nthAPL2 n (APL x1 x2) y z = APL (APL (APL (nth n x1) (nth n x2)) (nth n y)) (nth n z)
 nthAPL2 n (SMB s) y z = if (s eq "H") then (repeat n y z) else (APL (APL (SMB s) (nth n y)) (nth n z))
 
 OrdOfRepN : Nat -> Proof -> Ord
 OrdOfRep1 : Nat -> Proof -> Ord
 OrdOfRepApl : Nat -> Proof -> Proof -> Ord
 OrdOfRepN O x = Zero
 OrdOfRepN (1+ n) x = OrdOfRep1 n x
 -- OrdOfRep x = OrdOfRep1 (red x)
 OrdOfRep1 n AXM  = Zero
 OrdOfRep1 n (SMB s) = Zero
 OrdOfRep1 n DB0 = Zero
 OrdOfRep1 n (DBS x) = Zero
 OrdOfRep1 n (DBL x) = Zero
 OrdOfRep1 n (APL x y) = OrdOfRepApl n x y
 OrdOfRep1 n (LTR x y) = Zero
 OrdOfRepApl n AXM y = Zero
 OrdOfRepApl n DB0 y = Zero
 OrdOfRepApl n (DBS x) y = Zero
 OrdOfRepApl n (DBL x) y = Zero
 OrdOfRepApl n (LTR x1 x2) y = Zero
 OrdOfRepApl n (SMB s) y = if (s eq "Suc") then (Suc (OrdOfRepN n y)) else Zero
 OrdOfRepApl n (APL x1 x2) y = Lim (\p -> OrdOfRepN n (nth p (APL (APL x1 x2) y)))

 OrdOfRep : Proof -> Ord
 OrdOfRep x = OrdOfRepN 10000 x

