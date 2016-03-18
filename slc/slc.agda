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
 
 -- data Symbol : Set where
 --  Z : Symbol

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
 
 data Proof : Set where
  SYM : String -> Proof
  EA : Proof
  DBV : Nat -> Proof
  DBL : Proof -> Proof
  APL : Proof -> Proof -> Proof
  LTS : Proof -> Proof -> Proof
  SUB : Proof -> Proof -> Proof
  RED : Proof -> Proof
-- EQU : Proof -> Proof -> Proof
  MP : Proof
  RUL : String -> Proof

 data ProvedEq : Set where
  _proves_equals_ : Proof -> Proof -> Proof -> ProvedEq

 _===_ : Proof -> Proof -> Bool
 SYM n === SYM p = n eq p
 EA === EA = true
 DBV n === DBV p = n == p
 DBL x === DBL y = x === y
 APL x y === APL x' y' = (x === x') and (y === y')
 LTS x y === LTS x' y' = (x === x') and (y === y')
 SUB x y === SUB x' y' = (x === x') and (y === y')
 RED x === RED y = x === y
-- EQU x y === EQU x' y' = (x === x') and (y === y')
 MP === MP = true
 RUL r === RUL s = r eq s
 x === y = false

 shift : Nat -> Nat -> Proof -> Proof
 shift m n (SYM x) = SYM x
 shift m n EA = EA
 shift m n (DBV p) = if p >= m then DBV (n + p) else DBV p
 shift m n (DBL x) = DBL (shift (1+ m) n x)
 shift m n (APL x y) = APL (shift m n x) (shift m n y)
 shift m n (LTS x y) = LTS (shift m n x) (shift m n y)
 shift m n (SUB x y) = SUB (shift m n x) (shift m n y)
 shift m n (RED x) = RED (shift m n x)
-- shift m n (EQU x y) = EQU (shift m n x) (shift m n y)
 shift m n MP = MP
 shift m n (RUL r) = (RUL r)

 subst : Nat -> Proof -> Proof -> Proof
 subst n (SYM x) y = SYM x
 subst n EA y = EA
 subst n (DBV p) x = if p == n then x else (if p >= (1+ n) then DBV (p - (1+ O)) else DBV p)
 subst n (DBL x) y = DBL (subst (1+ n) x (shift O (1+ O) y))
 subst n (APL x y) z = APL (subst n x z) (subst n y z)
 subst n (LTS x y) z = LTS (subst n x z) (subst n y z)
 subst n (SUB x y) z = SUB (subst n x z) (subst n y z)
 subst n (RED x) z = RED (subst n x z)
-- subst n (EQU x y) z = EQU (subst n x z) (subst n y z)
 subst n MP z = MP
 subst n (RUL r) z = (RUL r)

 red1 : Proof -> Proof
 red1 (SYM x) = (SYM x)
 red1 EA = EA
 red1 (DBV n) = DBV n
 red1 (DBL x) = DBL (red1 x)
 red1 (APL (DBL x) y) = subst O x y
 red1 (APL x y) = APL (red1 x) (red1 y)
 red1 (LTS x y) = LTS (red1 x) (red1 y)
 red1 (SUB x y) = SUB (red1 x) (red1 y)
 red1 (RED x) = RED (red1 x)
 red1 MP = MP
 red1 (RUL r) = RUL r

 red : Nat -> Proof -> Proof
 red O x = x
 red (1+ n) x = if (red1 x) === x then x else red n (red1 x)

 _contSym_ : Proof -> String -> Bool
 SYM s contSym s' = s eq s'
 EA contSym s = false
 (DBV _) contSym _ = false
 (DBL x) contSym s = x contSym s
 (APL x y) contSym s = (x contSym s) or (y contSym s)
 (LTS x y) contSym s = (x contSym s) or (y contSym s)
 (SUB x y) contSym s = (x contSym s) or (y contSym s)
 (RED x) contSym s = x contSym s
 MP contSym s = false
 (RUL r) contSym s = false

 abstr : Nat -> String -> Proof -> Proof
 abst : Nat -> String -> Proof -> Proof
 abstr n s (SYM x) = if s eq x then DBV n else SYM x
 abstr n s (DBL x) = DBL (abst (1+ n) s x)
 abstr n s EA = EA
 abstr n s (DBV p) = DBV p
 abstr n s (APL x y) = APL (abst n s x) (abst n s y)
 abstr n s (LTS x y) = LTS (abst n s x) (abst n s y)
 abstr n s (SUB x y) = SUB (abst n s x) (abst n s y)
 abstr n s (RED x) = RED (abst n s x)
 abstr n s MP = MP          
 abstr n s (RUL r) = RUL r
 -- abst : Nat -> String -> Proof -> Proof
 abst n s x = if x contSym s then abstr n s x else x

 lambda : String -> Proof -> Proof
 lambda s x = DBL (abst 0 s x)

 side : Bool -> Proof -> Proof
 side _ (SYM n) = (SYM n)
 side _ EA = EA
 side _ (DBV n) = (DBV n)
 side s (DBL x) = DBL (side s x)
 side s (APL x y) = APL (side s x) (side s y)
-- side false (EQU x y) = x
-- side true (EQU x y) = y
 side s (LTS x y) = if (side false x) === (side false y) then (if s then side true y else side true x) else LTS x y
 side false (SUB x y) = APL (DBL x) y
 side true (SUB x y) = subst O x y
 side s (RED x) = red 10000 (side s x)
 side false MP = DBL (DBL (APL (APL (APL EA (DBV (1+ O))) (DBV (1+ O))) (DBV O)))
 side true MP = DBL (DBL (DBV O))
 side false (RUL "gparent") = lambda "x" (lambda "y" (lambda "z" (APL (APL (APL (SYM "parent") (SYM "x")) (SYM "y")) (APL (APL (APL (SYM "parent") (SYM "y")) (SYM "z")) (APL (APL (SYM "gparent") (SYM "x")) (SYM "z"))))))
 side true (RUL "gparent") = lambda "x" (lambda "y" (lambda "z" (DBL (DBV O))))
 side false (RUL "axiom1") = APL (APL (SYM "parent") (SYM "Allan")) (SYM "Brenda")
 side true (RUL "axiom1") = DBL (DBV O)
 side false (RUL "axiom2") = APL (APL (SYM "parent") (SYM "Brenda")) (SYM "Charles")
 side true (RUL "axiom2") = DBL (DBV O)
 side _ x = x
 
 repNat : Nat -> String
 repNat O = "O"
 repNat (1+ n) = (repNat n) cat "'"
 
 rep : Proof -> String
 rep (SYM s) = s
 rep EA = "EA"
 rep (DBV n) = "$" cat (repNat n)
 rep (DBL x) = "[" cat (rep x) cat "]"
 rep (APL x y) = "(" cat (rep x) cat " " cat (rep y) cat ")"
 rep (LTS x y) = "(LTS " cat (rep x) cat " " cat (rep y) cat ")"
 rep (SUB x y) = "(SUB " cat (rep x) cat " " cat (rep y) cat ")"
 rep (RED x) = "(RED " cat (rep x) cat ")"
 rep MP = "MP"
 rep (RUL r) = r

 develop : Proof -> ProvedEq
 develop p = p proves side false p equals side true p

 -- example : ctrl-C ctrl-N develop (RED (APL (APL MP (SYM "a")) (SYM "b")))

 devRep : Proof -> String
 devRep p = (rep p) cat " |- " cat (rep (side false p)) cat " = " cat (rep (side true p))

 lemma1 = RED (APL (APL (APL (RUL "gparent") (SYM "Allan")) (SYM "Brenda")) (SYM "Charles"))
 lemma2 = RED (APL (RUL "axiom1") (APL (APL (APL (SYM "parent") (SYM "Brenda")) (SYM "Charles")) (APL (APL (SYM "gparent") (SYM "Allan")) (SYM "Charles"))))
 lemma3 = LTS lemma2 lemma1
 lemma4 = RED (APL (RUL "axiom2") (APL (APL (SYM "gparent") (SYM "Allan")) (SYM "Charles")))
 theorem1 = LTS lemma4 lemma3

 -- ctrl-C ctrl-N devRep theorem1
 -- "(LTS (RED (axiom2 ((gparent Allan) Charles))) (LTS (RED (axiom1 (((parent Brenda) Charles) ((gparent Allan) Charles)))) (RED (((gparent Allan) Brenda) Charles)))) |- ((gparent Allan) Charles) = [$O]"

