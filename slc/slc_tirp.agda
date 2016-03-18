module slc_tirp where

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

SLC-terms or proofs extends symbolic lambda-terms to represent both symbolic lambda-terms and proofs. To each SLC-term are associated two SLC-terms called left and right. A SLC-term is a proof of the equality of its left and its right : x proves left(x) = right(x). Symbolic lambda-terms are particular SLC-terms which represent both a symbolic lambda-term and the proof that this symbolic lambda-term equals itself. Left and right of a lambda-term is itself.

So, a SLC-term (or term) may be the same as a lambda-term, with the possibility of subterms being any SLC-term :
- a symbol : a proves a = a
- an indexed variable (DBV n) where n is a natural number which is the proof of (DBV n) = (DBV n)
- a function (DBL x) where x is a DBL-term
- an application (APL x y) where x and y are DBL-term : if x proves xl = xl and y proves yl = yr, then (AP x y) proves (AP xl yl) = (ap xr yr)
to which we add those extensions to represent proofs :
- (LTS x y) which expresses transitivity and symmetry of equality : if x proves l = xr and y proves l = yr then (LTS x y) proves (xr = yr)
- (SUB x y) proves (APL (DBL x) y) = z where z is the result of substituting in x the variables whose index equals the nesting level in DBL terms by y.
- To define the rules or axioms of a specific theory there are different possibilities :
   - a rule or axiom of the represented theory (RUL "name") or (AXN n) which asserts that x = y
   - a unique axiom AXM which asserts that a = b, several axioms are represented by <a1, ..., an> = <b1, ... , bn>  

This is a minimal set necessary to represent terms and proofs.
Other constructs may be added to simplify notations, for example :
- (RTS x y) which expresses transitivity and symmetry of equality : if x proves xl = r and y proves yl = r then (RTS x y) proves (xl = yl)
- (TRANS x y) which expresses transitivity of equality : if x proves xl = z and y proves z = yr then (TRANS x y) proves xl = yr
- (SYM x) which expresses symmetry of equality : if x proves (xl = xr) then (SYM x) proves xr = xl
- (REDR x) : reduce right : if x proves xl = xr and xr reduces to yr then (REDR x) proves xl = yr
- (RED x) : reduce left and right : if x proves xl = xr, xl reduces to yl and xr reduces to yr then (RED x) proves yl = yr

Reduction of a term is defined by iterating a reduction step which consists of substituting (APL (DBL x) y) by the result of the substitution in x of variables whose index equals to the nesting level in DBL terms by y.

Natural numbers can be represented by SLC-terms :
 proofOfNat : Nat -> Proof
 proofOfNat O = DBL (DBL (DBV (1+ O)))
 proofOfNat (1+ n) = DBL (DBL (APL (DBV O) (proofOfNat n)))

Reflection can be added to this system by adding new SLC-terms :
 - (QOT x) which assert that QOT x = QOT x
 - (EVQ x) : if x proves xl = xr then EVQ x proves (APL (SMB "eval") (QOT xl)) = xr 
 - (LFX a b x) which asserts that (APL (APL (APL (SMB "left") (QOT a)) (QOT b)) (QOT x)) = (QOT y) where y = left(x) with axioms : for all natural n : APL a n = APL b n
 - (RGX a b x) which asserts that (APL (APL (APL (SMB "right") (QOT a)) (QOT b)) (QOT x)) = (QOT z) where z = right(x) with axioms : for all natural n : APL a n = APL b n

The reflection principles asserts that if x proves xl = xr then the values of xl and xr are equal :
 reflx : Bool -> Proof -> Proof -> Proof
 reflx s a b = lambda "X" (if s then (eval (leftx a b X)) else (eval (rightx a b X)))

An ordinal is defined as 0, the successor of an ordinal, or the limit of a function which associates an ordinal to any natural number :
 data Ord : Set where
  Zero : Ord
  Suc : Ord -> Ord
  Lim : (Nat -> Ord) -> Ord

The reflection principle can then be iterated transfinitely :
 tirp : Ord -> (Nat -> Bool -> Proof) -> Nat -> Bool -> Proof
 tirp Zero a n s = a n s
 tirp (Suc x) a n s = pair (tirp x a n s) (reflx s (tirp x a n true) (tirp x a n false))
 tirp (Lim f) a n s = tirp (f (f2 n)) a (f1 n) s

where f1 and f2 are functions which associate to each natural number n a unique pair <f1 n, f2 n>.

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
  QOT : Proof -> Proof
  EVQ : Proof -> Proof
  SDQ : Proof -> Proof -> Proof
  LFT : Proof -> Proof 
  RGT : Proof -> Proof
  LFX : Proof -> Proof -> Proof -> Proof
  RGX : Proof -> Proof -> Proof -> Proof
  AXM : Proof
  AXN : Nat -> Proof
  RUL : String -> Proof
  
 data ProvedEq : Set where
  _proves_equals_ : Proof -> Proof -> Proof -> ProvedEq

 data ProvedEqX : Set where
  having_equals_proof_proves_equals_ : Proof -> Proof -> Proof -> Proof -> Proof -> ProvedEqX

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
 QOT x === QOT x' = x === x'
 EVQ x === EVQ x' = x === x'
 SDQ x y === SDQ x' y' = (x === x') and (y === y')
 LFT x === LFT x' = x === x'
 RGT x === RGT x' = x === x'
 LFX a b x === LFX a' b' x' = ((a === a') and (b === b')) and (x === x')
 RGX a b x === RGX a' b' x' = ((a === a') and (b === b')) and (x === x')
 AXM === AXM = true
 AXN n === AXN p = n == p
 RUL r === RUL s = r eq s
 x === y = false

 shift : Nat -> Proof -> Proof
 shift m (SMB x) = SMB x
 shift m (DBV p) = if p >= m then DBV (1+ p) else DBV p
 shift m (DBL x) = DBL (shift (1+ m) x)
 shift m (APL x y) = APL (shift m x) (shift m y)
 shift m (LTS x y) = LTS (shift m x) (shift m y)
 shift m (SUB x y) = SUB (shift m x) (shift m y)
 shift m (RED x) = RED (shift m x)
 shift m (QOT x) = QOT x
 shift m (EVQ x) = EVQ (shift m x)
 shift m (SDQ x y) = SDQ (shift m x) (shift m y)
 shift m (LFT x) = LFT (shift m x)
 shift m (RGT x) = RGT (shift m x)
 shift m (LFX a b x) = LFX (shift m a) (shift m b) (shift m x)
 shift m (RGX a b x) = RGX (shift m a) (shift m b) (shift m x)
 shift m AXM = AXM
 shift m (AXN n) = AXN n
 shift m (RUL r) = (RUL r)

-- variable substitution
 subst : Nat -> Proof -> Proof -> Proof
 subst n (SMB x) y = SMB x
 subst n (DBV p) x = if p == n then x else (if p >= (1+ n) then DBV (p - (1+ O)) else DBV p)
 subst n (DBL x) y = DBL (subst (1+ n) x (shift O y))
 subst n (APL x y) z = APL (subst n x z) (subst n y z)
 subst n (LTS x y) z = LTS (subst n x z) (subst n y z)
 subst n (SUB x y) z = SUB (subst n x z) (subst n y z)
 subst n (RED x) z = RED (subst n x z)
 subst n (QOT x) z = QOT x
 subst n (EVQ x) z = EVQ (subst n x z)
 subst n (SDQ x y) z = SDQ (subst n x z) (subst n y z)
 subst n (LFT x) z = LFT (subst n x z)
 subst n (RGT x) z = RGT (subst n x z)
 subst n (LFX a b x) z = LFX (subst n a z) (subst n b z) (subst n x z)
 subst n (RGX a b x) z = RGX (subst n a z) (subst n b z) (subst n x z)
 subst n AXM z = AXM
 subst n (AXN p) z = AXN p
 subst n (RUL r) z = (RUL r)

 proofOfNat : Nat -> Proof
 proofOfNat O = DBL (DBL (DBV (1+ O)))
 proofOfNat (1+ n) = DBL (DBL (APL (DBV O) (proofOfNat n)))

 quot : Proof -> Proof
 -- quot x = APL (SMB "quote") x
 quot x = QOT x

-- reduction
 red1 : Proof -> Proof
 red1 (APL (APL (APL (APL (APL (APL (APL (APL (APL (APL (APL (QOT (SMB n)) s) v) l) a) t) r) q) e) g) d) k) = APL s (SMB n)
 red1 (APL (APL (APL (APL (APL (APL (APL (APL (APL (APL (APL (QOT (DBV p)) s) v) l) a) t) r) q) e) g) d) k) = APL v (proofOfNat p)
 red1 (APL (APL (APL (APL (APL (APL (APL (APL (APL (APL (APL (QOT (DBL x)) s) v) l) a) t) r) q) e) g) d) k) = APL l (quot x)
 red1 (APL (APL (APL (APL (APL (APL (APL (APL (APL (APL (APL (QOT (APL x y)) s) v) l) a) t) r) q) e) g) d) k) = APL (APL a (quot x)) (quot y)
 red1 (APL (APL (APL (APL (APL (APL (APL (APL (APL (APL (APL (QOT (LTS x y)) s) v) l) a) t) r) q) e) g) d) k) = APL (APL t (quot x)) (quot y)
 red1 (APL (APL (APL (APL (APL (APL (APL (APL (APL (APL (APL (QOT (RED x)) s) v) l) a) t) r) q) e) g) d) k) = APL r (quot x)
 red1 (APL (APL (APL (APL (APL (APL (APL (APL (APL (APL (APL (QOT (QOT x)) s) v) l) a) t) r) q) e) g) d) k) = APL q (quot x)
 red1 (APL (APL (APL (APL (APL (APL (APL (APL (APL (APL (APL (QOT (EVQ x)) s) v) l) a) t) r) q) e) g) d) k) = APL e (quot x)
-- red1 (APL (APL (APL (APL (APL (APL (APL (APL (APL (APL (SMB "quote") (LFT x)) s) v) l) a) t) r) g) d) e) = APL g (quot x)
-- red1 (APL (APL (APL (APL (APL (APL (APL (APL (APL (APL (SMB "quote") (RGT x)) s) v) l) a) t) r) g) d) e) = APL d (quot x)
-- red1 (APL (APL (APL (APL (APL (APL (APL (APL (APL (APL (SMB "quote") (RUL n)) s) v) l) a) t) r) g) d) e) = APL e (SMB n)
 red1 (APL (APL (APL (APL (APL (APL (APL (APL (APL (APL (APL (QOT (LFX a' b' x)) s) v) l) a) t) r) q) e) g) d) k) = APL (APL (APL g (quot a')) (quot b')) (quot x)
 red1 (APL (APL (APL (APL (APL (APL (APL (APL (APL (APL (APL (QOT (RGX a' b' x)) s) v) l) a) t) r) q) e) g) d) k) = APL (APL (APL d (quot a')) (quot b')) (quot x)
 red1 (APL (APL (APL (APL (APL (APL (APL (APL (APL (APL (APL (QOT (AXN n)) s) v) l) a) t) r) q) e) g) d) k) = APL k (proofOfNat n)
 red1 (SMB x) = (SMB x)
 red1 (DBV n) = DBV n
 red1 (DBL x) = DBL (red1 x)
 red1 (APL (DBL x) y) = subst O x y
 red1 (APL x y) = APL (red1 x) (red1 y)
 red1 (LTS x y) = LTS (red1 x) (red1 y)
 red1 (SUB x y) = SUB (red1 x) (red1 y)
 red1 (RED x) = RED (red1 x)
 red1 (QOT x) = QOT x
 red1 (EVQ x) = EVQ (red1 x)
 red1 (SDQ x y) = SDQ (red1 x) (red1 y)
 red1 (LFT x) = LFT (red1 x)
 red1 (RGT x) = RGT (red1 x)
 red1 (LFX a b x) = LFX (red1 a) (red1 b) (red1 x)
 red1 (RGX a b x) = RGX (red1 a) (red1 b) (red1 x) 
 red1 AXM = AXM
 red1 (AXN n) = AXN n
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
 (QOT x) contSym s = false
 (EVQ x) contSym s = x contSym s
 (SDQ x y) contSym s = (x contSym s) or (y contSym s)
 (LFT x) contSym s = x contSym s
 (RGT x) contSym s = x contSym s
 (LFX a b x) contSym s = ((a contSym s) or (b contSym s)) or (x contSym s)
 (RGX a b x) contSym s = ((a contSym s) or (b contSym s)) or (x contSym s)
 AXM contSym s = false
 AXN n contSym s = false
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
 abstr n s (QOT x) = QOT x
 abstr n s (EVQ x) = EVQ (abst n s x)
 abstr n s (SDQ x y) = SDQ (abst n s x) (abst n s y)       
 abstr n s (LFT x) = LFT (abst n s x)
 abstr n s (RGT x) = RGT (abst n s x) 
 abstr n s (LFX a b x) = LFX (abst n s a) (abst n s b) (abst n s x)
 abstr n s (RGX a b x) = RGX (abst n s a) (abst n s b) (abst n s x)
 abstr n s AXM = AXM
 abstr n s (AXN p) = AXN p
 abstr n s (RUL r) = RUL r
 abst n s x = if x contSym s then abstr n s x else x

 lambda : String -> Proof -> Proof
 lambda s x = DBL (abst 0 s x)

-- quot : Proof -> Proof
-- quot x = APL (SMB "quote") x

 eval : Proof -> Proof
 eval x = APL (SMB "eval") x

 sid : Proof -> Proof -> Proof
 sid x y = APL (APL (SMB "side") x) y

 left : Proof -> Proof
 left x = APL (SMB "left") x

 right : Proof -> Proof
 right x = APL (SMB "right") x

 leftx : Proof -> Proof -> Proof -> Proof
 leftx a b x = APL (APL (APL (SMB "leftx") a) b) x

 rightx : Proof -> Proof -> Proof -> Proof
 rightx a b x = APL (APL (APL (SMB "rightx") a) b) x

 T = DBL (DBV O)
-- F = DBL (DBL (DBV O))
 F = SMB "false"

 _|-_ : Proof -> Proof -> Proof
 p |- q = APL p q

 _=>_ : Proof -> Proof -> Proof
 p => q = APL (APL (SMB "imp") p) q

 all : Proof -> Proof
 all p = APL (SMB "all") p

 some : Proof -> Proof
 some p = APL (SMB "some") p

 eql : Proof -> Proof -> Proof
 eql x y = APL (APL (SMB "equal") x) y

 P = (SMB "P")
 Q = (SMB "Q")
 R = (SMB "R")
 X = (SMB "X")
 Y = (SMB "Y")
 Z = (SMB "Z")

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
 side s (QOT x) = QOT x
 side s (EVQ x) = if s then APL (SMB "eval") (QOT (side s x)) else side s x
-- side s (SDQ x y) = if s then (sid (side s x) (quot (side s y))) else (quot (side x y)) 
 side s (LFT x) = if s then left (quot x) else quot (side true x)
 -- side s (LFT x) = if s then left (quot (side s x)) else quot (side true (side s x))
 side s (RGT x) = if s then right (quot x) else quot (side false x)
 -- side s (RGT x) = if s then right (quot (side s x)) else quot (side false (side s x))
 side s (RUL "evq") = lambda "X" (if s then (eval (quot X)) else X)
 side s (RUL "equal") = lambda "X" (if s then (eql X X) else T)
 side s (RUL "refl") = lambda "X" (lambda "Y" (lambda "Z" (if s then (eql (left X) Y) |- ((eql (right X) Z) |- eql Y Z) else T)))
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
-- Propositional logic
 side s (RUL "mp") = lambda "P" (lambda "Q" (if s 
  then (P => Q) |- (P |- Q) 
  else T))
 side s (RUL "ak") = lambda "P" (lambda "Q" (if s
  then P => (Q => P)
  else T))
 side s (RUL "as") = lambda "P" (lambda "Q" (lambda "R" (if s
  then (P => (Q => R)) => ((P => Q) => (P => R))
  else T)))
 side s (RUL "efq") = lambda "P" (if s
  then (F => P)
  else T)
 side s (RUL "raa") = lambda "P" (if s
  then ((P => F) => F) => P
  else T)
 side s (RUL "gen") = lambda "P" (if s
  then P |- all (DBL P)
  else T)
 side s (RUL "part") = lambda "P" (lambda "X" (if s
  then ((all P) => (APL P X))
  else T))
 side s (RUL "permut") = lambda "P" (lambda "Q" (if s
  then (all (lambda "X" (P => (APL Q X)))) => (P => (all Q))
  else T))
 side s (RUL "some") = lambda "P" (if s
  then ((all P) => F) => ((APL P (some (lambda "X" ((APL P X) => F)))) => F)
  else T)
 side _ x = x

{-
 sidex : Bool -> Proof -> Proof -> Proof -> Proof
 sidex _ _ _ (SMB n) = (SMB n)
 sidex _ _ _ (DBV n) = (DBV n)
 sidex s a b (DBL x) = DBL (sidex s a b x)
 sidex s a b (APL x y) = APL (sidex s a b x) (sidex s a b y)
 sidex s a b (LTS x y) = if (sidex true a b x) === (sidex true a b y) then (if s then sidex false a b x else sidex false a b y) else LTS x y
 sidex true _ _ (SUB x y) = APL (DBL x) y
 sidex false _ _ (SUB x y) = subst O x y
 sidex s a b (RED x) = red 10000 (sidex s a b x)
-- side s (SDQ x y) = if s then (sid (side s x) (quot (side s y))) else (quot (side x y)) 
-- side s (LFT x) = if s then left (quot x) else quot (side true x)
 sidex s a b (LFX a' b' x) = if s then leftx (quot a') (quot b') (quot x) else quot (sidex true a' b' x)
 -- side s (LFT x) = if s then left (quot (side s x)) else quot (side true (side s x))
 sidex s a b (RGX a' b' x) = if s then rightx (quot a') (quot b') (quot x) else quot (sidex false a' b' x)
 -- side s (RGT x) = if s then right (quot (side s x)) else quot (side false (side s x))
 sidex s a b AXM = if s then a else b
 sidex s _ _ (RUL "evq") = lambda "X" (if s then (eval (quot X)) else X)
 sidex s _ _ (RUL "equal") = lambda "X" (if s then (eql X X) else T)
-- sidex s _ _ (RUL "refl") = lambda "X" (lambda "Y" (lambda "Z" (if s then (eql (left X) Y) |- ((eql (right X) Z) |- eql Y Z) else T)))
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
{-
 side true (RUL "gparent") = lambda "x" (lambda "y" (lambda "z" (APL (APL (APL (SMB "parent") (SMB "x")) (SMB "y")) (APL (APL (APL (SMB "parent") (SMB "y")) (SMB "z")) (APL (APL (SMB "gparent") (SMB "x")) (SMB "z"))))))
 side false (RUL "gparent") = lambda "x" (lambda "y" (lambda "z" (DBL (DBV O))))
 side true (RUL "axiom1") = APL (APL (SMB "parent") (SMB "Allan")) (SMB "Brenda")
 side false (RUL "axiom1") = DBL (DBV O)
 side true (RUL "axiom2") = APL (APL (SMB "parent") (SMB "Brenda")) (SMB "Charles")
 side false (RUL "axiom2") = DBL (DBV O)
-- Propositional logic
 side s (RUL "mp") = lambda "P" (lambda "Q" (if s 
  then (P => Q) |- (P |- Q) 
  else T))
 side s (RUL "ak") = lambda "P" (lambda "Q" (if s
  then P => (Q => P)
  else T))
 side s (RUL "as") = lambda "P" (lambda "Q" (lambda "R" (if s
  then (P => (Q => R)) => ((P => Q) => (P => R))
  else T)))
 side s (RUL "efq") = lambda "P" (if s
  then (F => P)
  else T)
 side s (RUL "raa") = lambda "P" (if s
  then ((P => F) => F) => P
  else T)
 side s (RUL "gen") = lambda "P" (if s
  then P |- all (DBL P)
  else T)
 side s (RUL "part") = lambda "P" (lambda "X" (if s
  then ((all P) => (APL P X))
  else T))
 side s (RUL "permut") = lambda "P" (lambda "Q" (if s
  then (all (lambda "X" (P => (APL Q X)))) => (P => (all Q))
  else T))
 side s (RUL "some") = lambda "P" (if s
  then ((all P) => F) => ((APL P (some (lambda "X" ((APL P X) => F)))) => F)
  else T)
-}
 sidex _ _ _ x = x
-}

-- sidex s a b x with axioms a i = b i
-- or sidex s a x whit axioms a i true = a i false

 sidex : Bool -> Proof -> Proof -> Proof -> Proof
 sidex _ _ _ (SMB n) = (SMB n)
 sidex _ _ _ (DBV n) = (DBV n)
 sidex s a b (DBL x) = DBL (sidex s a b x)
 sidex s a b (APL x y) = APL (sidex s a b x) (sidex s a b y)
 sidex s a b (LTS x y) = if (sidex true a b x) === (sidex true a b y) then (if s then sidex false a b x else sidex false a b y) else LTS x y
 sidex true _ _ (SUB x y) = APL (DBL x) y
 sidex false _ _ (SUB x y) = subst O x y
 sidex s a b (RED x) = red 10000 (sidex s a b x)
 sidex s a b (QOT x) = QOT x
 sidex s a b (EVQ x) = if s then APL (SMB "eval") (QOT (side s x)) else side s x
-- side s (SDQ x y) = if s then (sid (side s x) (quot (side s y))) else (quot (side x y)) 
-- side s (LFT x) = if s then left (quot x) else quot (side true x)
------ sidex s a b (LFX a' b' x) = if s then leftx (quot a') (quot b') (quot x) else quot (sidex true a' b' x)
 sidex s a b (LFX a' b' x) = if s then leftx (quot a') (quot b') (quot x) else quot (sidex true a' b' x)
 -- side s (LFT x) = if s then left (quot (side s x)) else quot (side true (side s x))
------ sidex s a b (RGX a' b' x) = if s then rightx (quot a') (quot b') (quot x) else quot (sidex false a' b' x)
 sidex s a b (RGX a' b' x) = if s then rightx (quot a') (quot b') (quot x) else quot (sidex false a' b' x)
 -- side s (RGT x) = if s then right (quot (side s x)) else quot (side false (side s x))
 -- sidex s a b AXM = if s then a else b
 sidex s a b (AXN n) = if s then (APL a (proofOfNat n)) else (APL b (proofOfNat n))
 sidex s _ _ (RUL "evq") = lambda "X" (if s then (eval (quot X)) else X)
 sidex s _ _ (RUL "equal") = lambda "X" (if s then (eql X X) else T)
-- sidex s _ _ (RUL "refl") = lambda "X" (lambda "Y" (lambda "Z" (if s then (eql (left X) Y) |- ((eql (right X) Z) |- eql Y Z) else T)))
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
{-
 side true (RUL "gparent") = lambda "x" (lambda "y" (lambda "z" (APL (APL (APL (SMB "parent") (SMB "x")) (SMB "y")) (APL (APL (APL (SMB "parent") (SMB "y")) (SMB "z")) (APL (APL (SMB "gparent") (SMB "x")) (SMB "z"))))))
 side false (RUL "gparent") = lambda "x" (lambda "y" (lambda "z" (DBL (DBV O))))
 side true (RUL "axiom1") = APL (APL (SMB "parent") (SMB "Allan")) (SMB "Brenda")
 side false (RUL "axiom1") = DBL (DBV O)
 side true (RUL "axiom2") = APL (APL (SMB "parent") (SMB "Brenda")) (SMB "Charles")
 side false (RUL "axiom2") = DBL (DBV O)
-- Propositional logic
 side s (RUL "mp") = lambda "P" (lambda "Q" (if s 
  then (P => Q) |- (P |- Q) 
  else T))
 side s (RUL "ak") = lambda "P" (lambda "Q" (if s
  then P => (Q => P)
  else T))
 side s (RUL "as") = lambda "P" (lambda "Q" (lambda "R" (if s
  then (P => (Q => R)) => ((P => Q) => (P => R))
  else T)))
 side s (RUL "efq") = lambda "P" (if s
  then (F => P)
  else T)
 side s (RUL "raa") = lambda "P" (if s
  then ((P => F) => F) => P
  else T)
 side s (RUL "gen") = lambda "P" (if s
  then P |- all (DBL P)
  else T)
 side s (RUL "part") = lambda "P" (lambda "X" (if s
  then ((all P) => (APL P X))
  else T))
 side s (RUL "permut") = lambda "P" (lambda "Q" (if s
  then (all (lambda "X" (P => (APL Q X)))) => (P => (all Q))
  else T))
 side s (RUL "some") = lambda "P" (if s
  then ((all P) => F) => ((APL P (some (lambda "X" ((APL P X) => F)))) => F)
  else T)
-}
 sidex _ _ _ x = x


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
 rep (QOT x) = "'" cat (rep x)
 rep (EVQ x) = "(EVQ " cat rep x cat ")"
 rep (SDQ x y) = "(SDQ " cat (rep x) cat " " cat (rep y) cat ")"
 rep (LFT x) = "(LFT " cat (rep x) cat ")"
 rep (RGT x) = "(RGT " cat (rep x) cat ")"
 rep (LFX a b x) = "(LFX " cat rep a cat " " cat rep b cat " " cat rep x cat ")"
 rep (RGX a b x) = "(RGX " cat rep a cat " " cat rep b cat " " cat rep x cat ")"
 rep AXM = "AXM"
 rep (AXN n) = "#" cat (repNat n)
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

 developx : Proof -> Proof -> Proof -> ProvedEqX
 developx a b p = having a equals b proof p proves sidex true a b p equals sidex false a b p


 A1 = lambda "x" (lambda "y" (lambda "z" (APL (APL (APL (SMB "parent") (SMB "x")) (SMB "y")) (APL (APL (APL (SMB "parent") (SMB "y")) (SMB "z")) (APL (APL (SMB "gparent") (SMB "x")) (SMB "z"))))))
 B1 = lambda "x" (lambda "y" (lambda "z" (DBL (DBV O))))
 A2 = APL (APL (SMB "parent") (SMB "Allan")) (SMB "Brenda")
 B2 = DBL (DBV O)
 A3 = APL (APL (SMB "parent") (SMB "Brenda")) (SMB "Charles")
 B3 = DBL (DBV O)

 A = lambda "X" (APL (APL (APL X A1) A2) A3)
 B = lambda "X" (APL (APL (APL X B1) B2) B3)

 RuleGparent = APL AXM (DBL (DBL (DBL (DBV 2))))
 RuleAxiom1 = APL AXM (DBL (DBL (DBL (DBV 1))))
 RuleAxiom2 = APL AXM (DBL (DBL (DBL (DBV 0))))

 lemma1x = RED (APL (APL (APL RuleGparent (SMB "Allan")) (SMB "Brenda")) (SMB "Charles"))
 lemma2x = RED (APL RuleAxiom1 (APL (APL (APL (SMB "parent") (SMB "Brenda")) (SMB "Charles")) (APL (APL (SMB "gparent") (SMB "Allan")) (SMB "Charles"))))
 lemma3x = LTS lemma2 lemma1
 lemma4x = RED (APL RuleAxiom2 (APL (APL (SMB "gparent") (SMB "Allan")) (SMB "Charles")))
 theorem1x = LTS lemma4 lemma3

-- To display the proof under Emacs type :
-- ctrl-C ctrl-N developx A B theorem1x

 reflx1 : Bool -> Proof -> Proof -> Proof
-- reflx s a b = lambda "X" (lambda "Y" (lambda "Z" (if s then (eql (leftx a b X) Y) |- ((eql (rightx a b X) Z) |- eql Y Z) else T)))
 reflx1 s a b = lambda "X" (lambda "Y" (lambda "Z" (if s then (eql (leftx a b X) Y) |- ((eql (rightx a b X) Z) |- eql (eval Y) (eval Z)) else T)))

 reflx : Bool -> Proof -> Proof -> Proof
 reflx s a b = lambda "X" (if s then (eval (leftx a b X)) else (eval (rightx a b X)))

-- Ordinals

 data Ord : Set where
  Zero : Ord
  Suc : Ord -> Ord
  Lim : (Nat -> Ord) -> Ord

 suc : Ord -> Ord
 suc x = Suc x

 lim' : (Nat -> Ord) -> Ord
 lim' f = Lim f

 OrdNat : Nat -> Ord
 OrdNat O = Zero
 OrdNat (1+ n) = Suc (OrdNat n)

 lim : (Ord -> Ord) -> Ord
 lim f = Lim (\(n  : Nat) -> f (OrdNat n))

 One : Ord
 One = Suc Zero
 
 omega : Ord
 omega = Lim OrdNat

 repeat : (a : Set) -> (n : Nat) -> (f : a -> a) -> (x : a) -> a
 repeat _ O f x = x
 repeat a (1+ p) f x = repeat a p f (f x)

 -- representation of naturals
 rep1 : {t : Set} -> t -> (t -> t) -> Nat -> t
 rep1 z s O = z
 rep1 z s (1+ x) = s (rep1 z s x) 

 rep' : (t : Set) -> t -> (t -> t) -> Nat -> t
 rep' _ z s O = z
 rep' t z s (1+ x) = s (rep' t z s x) 

-- rep : {t : Set} -> t -> (t -> t) -> Nat -> t
-- rep = rep' _

 re : {t : Set} -> (t -> t) -> t -> Nat -> t
 re s z = rep' _ z s

 -- repr : {t : Set} -> Nat -> (t -> t) -> t
 -- repr n s z = re s z n
 
 repr' : (t : Set) -> Nat -> (t -> t) -> t -> t
 repr' _ O s z = z
 repr' t (1+ n) s z = s (repr' t n s z)

 repr : {t : Set} -> Nat -> (t -> t) -> t -> t
 repr = repr' _

 rep'' : (t : Set) -> t -> (t -> t) -> Nat -> t
 rep'' _ z s O = z
 rep'' t z s (1+ x) = rep'' t (s z) s x

 -- representation of ordinals
 Rep : Ord -> (Ord -> Ord) -> Ord -> Ord
 Rep z s Zero = z
 Rep z s (Suc x) = s (Rep z s x)
 Rep z s (Lim f) = Lim (\(x : Nat) -> Rep z s (f x))

 Re : (Ord -> Ord) -> Ord -> Ord -> Ord
 Re s z Zero = z
 Re s z (Suc x) = s (Re s z x)
 Re s z (Lim f) = Lim (\n -> Re s z (f n))

 Repr : Ord -> (Ord -> Ord) -> Ord -> Ord
 Repr Zero s z = z
 Repr (Suc n) s z = s (Repr n s z)
 Repr (Lim f) s z = Lim (\n -> Repr (f n) s z)
 
{-
 Rep' : (t : Set) -> t -> (t -> t) -> Ord -> t
 Rep' _ z s Zero = z
 Rep' t z s (Suc x) = s (Rep' t z s x)
 Rep' t z s (Lim f) = Lim (\(x : Nat) -> Rep' t z s (f x))
-}

{-
 + : Nat -> Nat -> Nat
 + O y = y
 + (1+ x) y = 1+ (+ x y)
-}

 plus : Ord -> Ord -> Ord
 plus Zero y = y
 plus (Suc x) y = Suc (plus x y)
 plus (Lim f) y = Lim (\(x : Nat) -> plus (f x) y)

 times : Ord -> Ord -> Ord
 times Zero y = y
 times (Suc x) y = plus y (times x y)
 times (Lim f) y = Lim (\(x : Nat) -> times (f x) y)

 power : Ord -> Ord -> Ord
 power Zero y = One
 power (Suc x) y = times y (power x y)
 power (Lim f) y = Lim (\(x : Nat) -> power (f x) y)

 hpower : Ord -> Ord -> Ord
 hpower Zero y = One
 hpower (Suc x) y = power y (hpower x y)
 hpower (Lim f) y = Lim (\(x : Nat) -> hpower (f x) y)

 plus' : Ord -> Ord -> Ord
 plus' a b = Rep b suc a

 times' : Ord -> Ord -> Ord
 times' a b = Rep Zero (plus' b) a

 power' : Ord -> Ord -> Ord
 power' a b = Rep (Suc Zero) (times' b) a

 op : Ord -> Ord -> Ord -> Ord
 op Zero x y = plus x y
 op (Suc Zero) x y = times x y
 op (Suc n) Zero y = One
 op (Suc n) (Suc Zero) y = y
 op (Suc n) (Suc x) y = op n y (op (Suc n) x y)
 op (Suc n) (Lim f) y = Lim (\(x : Nat) -> op (Suc n) (f x) y)
 op (Lim f) x y = Lim (\(n : Nat) -> op (f n) x y)
 
 op' : Ord -> Ord -> Ord -> Ord
 op' Zero x y = plus x y
 op' (Suc n) Zero y = y 
 op' (Suc n) (Suc x) y = op' n y (op' (Suc n) x y)
 op' (Suc n) (Lim f) y = Lim (\(x : Nat) -> op' (Suc n) (f x) y)
 op' (Lim f) x y = Lim (\(n : Nat) -> op' (f n) x y)

 epsilon0 : Ord
 epsilon0 = Lim (rep' _ Zero (\(x : Ord) -> power x omega))

 epsilon0' : Ord
 epsilon0' = hpower omega omega

 epsilon0'' : Ord
 epsilon0'' = op (Suc (Suc (Suc (Suc Zero)))) (Suc (Suc Zero)) omega

 H0 : (Ord -> Ord) -> Ord -> Ord
 H0 f x = Lim (rep' _ x f)
 -- H f x = Lim (\(n : Nat) -> repeat _ n f x)

 H0' : (Ord -> Ord) -> Ord -> Ord
 H0' f x = Lim (\n -> repr n f x)

 H' : {s : Set} -> (s -> Ord) -> (s -> s) -> s -> Ord
 H' phi f x = Lim (\(y : Nat) -> phi (rep' _ x f y))

 pair : Proof -> Proof -> Proof
 pair x y = lambda "X" (APL (APL X x) y)

 auto = lambda "X" (APL X X)
 comb = lambda "X" (lambda "Y" (lambda "Z" (APL X (APL Y Z))))
 fix = lambda "X" (APL auto (APL (APL comb X) auto))

 zerop = lambda "X" (lambda "Y" X)
 sucp = lambda "X" (lambda "Y" (lambda "Z" (APL Z (APL (APL X Y) Z))))

 seq = APL fix (lambda "X" (lambda "Y" (lambda "Z" (pair (APL Y Z) (APL (APL X Y) (APL sucp Z))))))

-- Transfinite iteration of reflection principle
{-
 tirp : Bool -> Proof -> Proof -> Ord -> Proof
 ff : Bool -> Proof -> Proof -> (Nat -> Ord) -> Proof
 -- tirpl : Bool -> Proof -> Proof -> (Nat -> Ord) -> Nat -> Proof
 tirp s a b Zero = if s then a else b
 tirp s a b (Suc x) = pair (tirp s a b x) (reflx s (tirp true a b x) (tirp false a b x)) 
 -- tirp s a b (Lim f) = tirpl s a b f 0
 -- tirpl s a b f n = pair (tirp s a b (f n)) (tirpl s a b f (1+ n))
 tirp s a b (Lim f) = APL (APL seq (ff s a b f)) zerop
 ff s a b f = DBL (tirp s a b (f (DBV O)))
-}

 mod2 : Nat -> Nat
 mod2 O = O
 mod2 (1+ O) = 1
 mod2 (1+ (1+ n)) = mod2 n

 div2 : Nat -> Nat
 div2 O = O
 div2 1 = O
 div2 (1+ (1+ n)) = 1+ (div2 n) 

 div4 : Nat -> Nat
 div4 O = O
 div4 1 = O
 div4 2 = O
 div4 3 = O
 div4 (1+ (1+ (1+ (1+ n)))) = 1+ (div4 n) 

 double : Nat -> Nat
 double n = n + n

{-
 f1 : Nat -> Nat
 f1 O = O
 f1 n = (mod2 n) + double (f1 (div4 n)) 

 f2 : Nat -> Nat
 f2 n = f1 (div2 n)
-}

 data NatList : Set where 
  nil : NatList
  cons : Nat -> NatList -> NatList

 sucDigits : NatList -> NatList
 sucDigits nil = cons 1 nil
 sucDigits (cons O l) = cons 1 l
 sucDigits (cons _ l) = cons O (sucDigits l)
 
 digits : Nat -> NatList
 digits O = nil
-- digits n = cons (mod2 n) (digits (div2 n))
 digits (1+ n) = sucDigits (digits n)

 evenDigits : NatList -> NatList
 evenDigits nil = nil
 evenDigits (cons x nil) = cons x nil
 evenDigits (cons x (cons _ l)) = cons x (evenDigits l)

 natOfDigits : NatList -> Nat
 natOfDigits nil = O
 natOfDigits (cons x l) = x + double (natOfDigits l)

 f1a : Nat -> Nat
 f1a n = natOfDigits (evenDigits (digits n))

 f2a : Nat -> Nat
 f2a n = f1a (div2 n)

 data NatPair : Set where 
  natPair : Nat -> Nat -> NatPair

 firstNat : NatPair -> Nat
 firstNat (natPair n p) = n

 secondNat : NatPair -> Nat
 secondNat (natPair n p) = p

 sucNatPair : NatPair -> NatPair
 sucNatPair n = if (firstNat n == O) then natPair (1+ (secondNat n)) O else natPair ((firstNat n) - 1) ((secondNat n) + 1)

 natPairOfNat : Nat -> NatPair
 natPairOfNat O = natPair O O
 natPairOfNat (1+ n) = sucNatPair (natPairOfNat n)

 f1 : Nat -> Nat
 f1 n = firstNat (natPairOfNat n)

 f2 : Nat -> Nat
 f2 n = secondNat (natPairOfNat n)

 tirp : Ord -> (Nat -> Bool -> Proof) -> Nat -> Bool -> Proof
 tirp Zero a n s = a n s
 tirp (Suc x) a n s = pair (tirp x a n s) (reflx s (tirp x a n true) (tirp x a n false))
 tirp (Lim f) a n s = tirp (f (f2 n)) a (f1 n) s


 
 


