module slc_parent where

{-
Symbolic Lambda Calculus in Agda 
by Jacques Bailhache 
April 10, 2015

SLC is a formal system for proving equality of terms called symbolic lambda-terms, in a theory represented by a set of axioms. Each axiom is an equality between two symbolic lambda-terms. A symbolic lambda-term is a lambda-term possibly including some symbols.
De Bruijn index notation is used to represent lambda-terms.

A lambda-term may be :
- a symbol
- an indexed variable (DBV n) where n is a natural number
- a function (DBL x) where x is a lambda-term
- an application (APL x y) where x and y are lambda-terms

Examples :
(DBL (DBV 0)) represents the identity function.
(APL (DBL (DBV 0)) a) represents the application of the identity function to the symbol a, which equals the symbol a.

More generally, (AP (DBL x) y) equals the result of substituting in x the variables whose index equals their level of nesting in DBL terms by y.

For an easier reading, classical lambda-calculus will be used sometimes, but it may be easily translated into De Bruijn index notation.
For example:
(APL f x) = x
is equivalent to :
f = (lambda x x)
or :
f = (DBL (DBV 0))

SLC-terms extends symbolic lambda-terms to represent both symbolic lambda-terms and proofs. To each SLC-term are associated two SLC-terms called left and right. A SLC-term is a proof of the equality of its left and its right : x proves left(x) = right(x). Symbolic lambda-terms are particular SLC-terms which represent both a symbolic lambda-term and the proof that this symbolic lambda-term equals itself. Left and right of a lambda-term is itself.

So, a SLC-term (or term) may be the same as a lambda-term, with the possibility of subterms being any SLC-term :
- a symbol : a proves a = a
- an indexed variable (DBV n) where n is a natural number which is the proof of (DBV n) = (DBV n)
- a function (DBL x) where x is a DBL-term
- an application (APL x y) where x and y are DBL-term : if x proves xl = xl and y proves yl = yr, then (AP x y) proves (AP xl yl) = (ap xr yr)
to which we add those extensions to represent proofs :
- (LTS x y) which expresses transitivity and symmetry of equality : if x proves l = xr and y proves l = yr then (LTS x y) proves (xr = yr)
- (SUB x y) proves (APL (DBL x) y) = z where z is the result of substituting in x the variables whose index equals the nesting level in DBL terms by y.
- a rule or axiom of the represented theory (RUL "name") which asserts that x = y

This is a minimal set necessary to represent terms and proofs.
Other constructs may be added to simplify notations, for example :
- (RTS x y) which expresses transitivity and symmetry of equality : if x proves xl = r and y proves yl = r then (RTS x y) proves (xl = yl)
- (TRANS x y) which expresses transitivity of equality : if x proves xl = z and y proves z = yr then (TRANS x y) proves xl = yr
- (SYM x) which expresses symmetry of equality : if x proves (xl = xr) then (SYM x) proves xr = xl
- (REDR x) : reduce right : if x proves xl = xr and xr reduces to yr then (REDR x) proves xl = yr
- (RED x) : reduce left and right : if x proves xl = xr, xl reduces to yl and xr reduces to yr then (RED x) proves yl = yr

Reduction of a term is defined by iterating a reduction step which consists of substituting (APL (DBL x) y) by the result of the substitution in x of variables whose index equals to the nesting level in DBL terms by y.

-}

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
  SMB : String -> Proof
  DBV : Nat -> Proof
  DBL : Proof -> Proof
  APL : Proof -> Proof -> Proof
  LTS : Proof -> Proof -> Proof
  SUB : Proof -> Proof -> Proof
  RED : Proof -> Proof
  RUL : String -> Proof

 data ProvedEq : Set where
  _proves_equals_ : Proof -> Proof -> Proof -> ProvedEq

-- Syntactic equality of proofs
 _===_ : Proof -> Proof -> Bool
 SMB n === SMB p = n eq p
 DBV n === DBV p = n == p
 DBL x === DBL y = x === y
 APL x y === APL x' y' = (x === x') and (y === y')
 LTS x y === LTS x' y' = (x === x') and (y === y')
 SUB x y === SUB x' y' = (x === x') and (y === y')
 RED x === RED y = x === y
-- EQU x y === EQU x' y' = (x === x') and (y === y')
 RUL r === RUL s = r eq s
 x === y = false

 shift : Nat -> Nat -> Proof -> Proof
 shift m n (SMB x) = SMB x
 shift m n (DBV p) = if p >= m then DBV (n + p) else DBV p
 shift m n (DBL x) = DBL (shift (1+ m) n x)
 shift m n (APL x y) = APL (shift m n x) (shift m n y)
 shift m n (LTS x y) = LTS (shift m n x) (shift m n y)
 shift m n (SUB x y) = SUB (shift m n x) (shift m n y)
 shift m n (RED x) = RED (shift m n x)
 shift m n (RUL r) = (RUL r)

-- variable substitution
 subst : Nat -> Proof -> Proof -> Proof
 subst n (SMB x) y = SMB x
 subst n (DBV p) x = if p == n then x else (if p >= (1+ n) then DBV (p - (1+ O)) else DBV p)
 subst n (DBL x) y = DBL (subst (1+ n) x (shift O (1+ O) y))
 subst n (APL x y) z = APL (subst n x z) (subst n y z)
 subst n (LTS x y) z = LTS (subst n x z) (subst n y z)
 subst n (SUB x y) z = SUB (subst n x z) (subst n y z)
 subst n (RED x) z = RED (subst n x z)
 subst n (RUL r) z = (RUL r)

-- reduction
 red1 : Proof -> Proof
 red1 (SMB x) = (SMB x)
 red1 (DBV n) = DBV n
 red1 (DBL x) = DBL (red1 x)
 red1 (APL (DBL x) y) = subst O x y
 red1 (APL x y) = APL (red1 x) (red1 y)
 red1 (LTS x y) = LTS (red1 x) (red1 y)
 red1 (SUB x y) = SUB (red1 x) (red1 y)
 red1 (RED x) = RED (red1 x)
 red1 (RUL r) = RUL r

 red : Nat -> Proof -> Proof
 red O x = x
 red (1+ n) x = if (red1 x) === x then x else red n (red1 x)

-- does a proof contain a symbol ?
 _contSym_ : Proof -> String -> Bool
 SMB s contSym s' = s eq s'
 (DBV _) contSym _ = false
 (DBL x) contSym s = x contSym s
 (APL x y) contSym s = (x contSym s) or (y contSym s)
 (LTS x y) contSym s = (x contSym s) or (y contSym s)
 (SUB x y) contSym s = (x contSym s) or (y contSym s)
 (RED x) contSym s = x contSym s
 (RUL r) contSym s = false

-- abstraction
 abstr : Nat -> String -> Proof -> Proof
 abst : Nat -> String -> Proof -> Proof
 abstr n s (SMB x) = if s eq x then DBV n else SMB x
 abstr n s (DBL x) = DBL (abst (1+ n) s x)
 abstr n s (DBV p) = DBV p
 abstr n s (APL x y) = APL (abst n s x) (abst n s y)
 abstr n s (LTS x y) = LTS (abst n s x) (abst n s y)
 abstr n s (SUB x y) = SUB (abst n s x) (abst n s y)
 abstr n s (RED x) = RED (abst n s x)         
 abstr n s (RUL r) = RUL r
 abst n s x = if x contSym s then abstr n s x else x

 lambda : String -> Proof -> Proof
 lambda s x = DBL (abst 0 s x)

-- side true p = x and side false p = y means p proves x = y
 side : Bool -> Proof -> Proof
 side _ (SMB n) = (SMB n)
 side _ (DBV n) = (DBV n)
 side s (DBL x) = DBL (side s x)
 side s (APL x y) = APL (side s x) (side s y)
 side s (LTS x y) = if (side true x) === (side true y) then (if s then side false x else side false y) else LTS x y
 side true (SUB x y) = APL (DBL x) y
 side false (SUB x y) = subst O x y
 side s (RED x) = red 10000 (side s x)
{-
 Example of theory :
  1 rule :
   "gparent" : if parent x y and parent y z then gparent x z
  2 axioms :
   "axiom1" : parent Allan Brenda
   "axiom2" : parent Brenda Charles
 Truth of proposition p is represented by p = DBL (DBV O) = I (the identity combinator).
 Implication p => q is represented by (APL p q).
 If APL p q = I and p = I then APL I q = I then q = I.
-}
 side true (RUL "gparent") = lambda "x" (lambda "y" (lambda "z" (APL (APL (APL (SMB "parent") (SMB "x")) (SMB "y")) (APL (APL (APL (SMB "parent") (SMB "y")) (SMB "z")) (APL (APL (SMB "gparent") (SMB "x")) (SMB "z"))))))
 side false (RUL "gparent") = lambda "x" (lambda "y" (lambda "z" (DBL (DBV O))))
 side true (RUL "axiom1") = APL (APL (SMB "parent") (SMB "Allan")) (SMB "Brenda")
 side false (RUL "axiom1") = DBL (DBV O)
 side true (RUL "axiom2") = APL (APL (SMB "parent") (SMB "Brenda")) (SMB "Charles")
 side false (RUL "axiom2") = DBL (DBV O)
 side _ x = x
 
-- representation of proofs by strings

 repNat : Nat -> String
 repNat O = "O"
 repNat (1+ n) = (repNat n) cat "'"
 
 rep : Proof -> String
 rep (SMB s) = s
 rep (DBV n) = "$" cat (repNat n)
 rep (DBL x) = "[" cat (rep x) cat "]"
 rep (APL x y) = "(" cat (rep x) cat " " cat (rep y) cat ")"
 rep (LTS x y) = "(LTS " cat (rep x) cat " " cat (rep y) cat ")"
 rep (SUB x y) = "(SUB " cat (rep x) cat " " cat (rep y) cat ")"
 rep (RED x) = "(RED " cat (rep x) cat ")"
 rep (RUL r) = r

 develop : Proof -> ProvedEq
 develop p = p proves side true p equals side false p

 devRep : Proof -> String
 devRep p = (rep p) cat " |- " cat (rep (side true p)) cat " = " cat (rep (side false p))

-- Example of a proof that gparent Allan Charles is true

 lemma1 = RED (APL (APL (APL (RUL "gparent") (SMB "Allan")) (SMB "Brenda")) (SMB "Charles"))
 lemma2 = RED (APL (RUL "axiom1") (APL (APL (APL (SMB "parent") (SMB "Brenda")) (SMB "Charles")) (APL (APL (SMB "gparent") (SMB "Allan")) (SMB "Charles"))))
 lemma3 = LTS lemma2 lemma1
 lemma4 = RED (APL (RUL "axiom2") (APL (APL (SMB "gparent") (SMB "Allan")) (SMB "Charles")))
 theorem1 = LTS lemma4 lemma3

-- To display the proof under Emacs type :
-- ctrl-C ctrl-N devRep theorem1
-- "(LTS (RED (axiom2 ((gparent Allan) Charles))) (LTS (RED (axiom1 (((parent Brenda) Charles) ((gparent Allan) Charles)))) (RED (((gparent Allan) Brenda) Charles)))) |- ((gparent Allan) Charles) = [$O]"

