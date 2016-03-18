module slc where

 I : {s : Set} -> s -> s
 I a = a

 K : {s t : Set} -> s -> t -> s
 K a b = a

 S : {s t u : Set} -> (s -> t -> u) -> (s -> t) -> (s -> u)
 S a b c = a c (b c)

 C : {s t u : Set} -> (s -> t -> u) -> (t -> s -> u) 
 C a b c = a c b

 B : {s t u : Set} -> (s -> t) -> (u -> s) -> (u -> t)
 B a b c = a (b c)

 W : {s t u : Set} -> (s -> s -> t) -> (s -> t)
 W a b = a b b
 
 KI : {s t : Set} -> t -> s -> s
 KI = K I

 CI : {s t : Set} -> s -> (s -> t) -> t
 CI = C I

 data Bool : Set where
  true : Bool
  false : Bool

 if_then_else_ : {A : Set} -> Bool -> A -> A -> A
 if true then x else y = x
 if false then x else y = y

 _and_ : Bool -> Bool -> Bool
 true and x = x
 false and x = false

 data Nat : Set where
  O : Nat
  1+ : Nat -> Nat

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
 
 -- data Symbol : Set where
 --  Z : Symbol

 data Proof : Set where
  SYM : Nat -> Proof
  DBV : Nat -> Proof
  DBL : Proof -> Proof
  APL : Proof -> Proof -> Proof
  LTS : Proof -> Proof -> Proof
  SUB : Proof -> Proof -> Proof
  EQU : Proof -> Proof -> Proof

 _===_ : Proof -> Proof -> Bool
 SYM n === SYM p = n == p
 DBV n === DBV p = n == p
 DBL x === DBL y = x === y
 APL x y === APL x' y' = (x === x') and (y === y')
 LTS x y === LTS x' y' = (x === x') and (y === y')
 SUB x y === SUB x' y' = (x === x') and (y === y')
 EQU x y === EQU x' y' = (x === x') and (y === y')
 x === y = false

 shift : Nat -> Nat -> Proof -> Proof
 shift m n (SYM x) = SYM x
 shift m n (DBV p) = if p >= m then DBV (n + p) else DBV p
 shift m n (DBL x) = DBL (shift (1+ m) n x)
 shift m n (APL x y) = APL (shift m n x) (shift m n y)
 shift m n (LTS x y) = LTS (shift m n x) (shift m n y)
 shift m n (SUB x y) = SUB (shift m n x) (shift m n y)
 shift m n (EQU x y) = EQU (shift m n x) (shift m n y)

 subst : Nat -> Proof -> Proof -> Proof
 subst n (SYM x) y = SYM x
 subst n (DBV p) x = if p == n then x else (if p >= (1+ n) then DBV (p - (1+ O)) else DBV p)
 subst n (DBL x) y = DBL (subst (1+ n) x (shift O (1+ O) y))
 subst n (APL x y) z = APL (subst n x z) (subst n y z)
 subst n (LTS x y) z = LTS (subst n x z) (subst n y z)
 subst n (SUB x y) z = SUB (subst n x z) (subst n y z)
 subst n (EQU x y) z = EQU (subst n x z) (subst n y z)

 side : Bool -> Proof -> Proof
 side _ (SYM n) = (SYM n)
 side _ (DBV n) = (DBV n)
 side s (DBL x) = DBL (side s x)
 side s (APL x y) = APL (side s x) (side s y)
 side true (EQU x y) = x
 side false (EQU x y) = y
 side s (LTS x y) = if (side true x) === (side true y) then (if s then side false x else side false y) else LTS x y
 side true (SUB x y) = APL (DBL x) y
 side false (SUB x y) = subst O x y





