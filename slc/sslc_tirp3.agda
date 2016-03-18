module sslc_tirp where

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
 
-- SLC terms are proofs

 data Proof : Set where
  AXM : Proof
  SMB : Proof
  DB0 : Proof
  DBS : Proof -> Proof
  DBL : Proof -> Proof
  APL : Proof -> Proof -> Proof
  LTR : Proof -> Proof -> Proof

-- Syntactic equality of proofs
 _===_ : Proof -> Proof -> Bool
 SMB === SMB = true
 DB0 === DB0 = true
 DBS x === DBS y = x === y
 DBL x === DBL y = x === y
 APL x y === APL x' y' = (x === x') and (y === y')
 LTR x y === LTR x' y' = (x === x') and (y === y')
 AXM === AXM = true
 x === y = false

 shift : Proof -> Proof -> Proof
 shift u AXM = AXM
 shift u SMB = SMB
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
 subst1 u SMB b = SMB
 subst1 u DB0 b = DB0
 subst1 u (DBL x) b = DBL (subst (DBS u) x (shift DB0 b))
 subst1 u (DBS x) b = DBS (subst u x b)
 subst1 u (APL x y) b = APL (subst u x b) (subst u y b)
 subst1 u (LTR x y) b = LTR (subst u x b) (subst u y b)

 red1 : Proof -> Proof
 red1 AXM = AXM
 red1 SMB = SMB
 red1 DB0 = DB0
 red1 (DBS x) = DBS x
 red1 (DBL x) = DBL (red1 x)
 red1 (APL (DBL x) y) = subst (DB0) x y
 red1 (APL  x y) = APL (red1 x) (red1 y)
 red1 (LTR x y) = LTR (red1 x) (red1 y)

 redn : Nat -> Proof -> Proof
 redn O x = x
 redn (1+ n) x = if (red1 x) === x then x else redn n (red1 x)

 red : Proof -> Proof
 red a = redn 10000 a

 sidex : Bool -> Proof -> Proof -> Proof -> Proof
 sidex s a b AXM = if s then a else b
 sidex _ _ _ SMB = SMB
 sidex _ _ _ DB0 = DB0
 sidex _ _ _ (DBS x) = DBS x
 sidex s a b (DBL x) = DBL (sidex s a b x)
 sidex s a b (APL x y) = APL (sidex s a b x) (sidex s a b y)
 sidex s a b (LTR x y) = if red (sidex true a b x) === red (sidex true a b y) then (if s then red (sidex false a b x) else red (sidex false a b y)) else (LTR x y)

 -- sidex s a b (LTR x y) = if red (sidex true a b x) === red (sidex true a b y) then red (sidex false a b (if s then x else y)) else (LTR x y)


