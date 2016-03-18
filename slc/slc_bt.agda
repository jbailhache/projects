module slc_bt where

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

-- Binary trees

 data BinTree : Set where
  LEAF : BinTree
  NODE : BinTree -> BinTree -> BinTree

 data ProvedEq : Set where
  _proves_equals_ : BinTree -> BinTree -> BinTree -> ProvedEq

-- Syntactic equality 
 _===_ : BinTree -> BinTree -> Bool
 LEAF === LEAF = true
 LEAF === NODE _ _ = false
 NODE _ _ === LEAF = false
 NODE a b === NODE c d = (a === b) and (c === d)

{-
 Smb = LEAF
 Dbv = NODE LEAF LEAF
 Dbl = NODE (NODE LEAF LEAF) LEAF
 Apl = NODE LEAF (NODE LEAF LEAF)
 Lts = NODE (NODE LEAF LEAF) (NODE LEAF LEAF)
 Red = NODE (NODE (NODE LEAF LEAF) LEAF) LEAF
 Rul = NODE (NODE LEAF (NODE LEAF LEAF)) LEAF
-}

 Smb = NODE LEAF LEAF
 Dbv = NODE LEAF (NODE LEAF LEAF)
 Dbl = NODE LEAF (NODE (NODE LEAF LEAF) LEAF)
 Apl = NODE LEAF (NODE LEAF (NODE LEAF LEAF))
 Lts = NODE (NODE LEAF LEAF) (NODE LEAF (NODE LEAF LEAF))
 Red = NODE (NODE LEAF LEAF) (NODE (NODE LEAF LEAF) LEAF)
 Rul = NODE (NODE LEAF LEAF) LEAF

 BinTreeOfNat : Nat -> BinTree
 BinTreeOfNat O = LEAF
 BinTreeOfNat (1+ n) = NODE (BinTreeOfNat n) LEAF

 NatOfBinTree : BinTree -> Nat
 NatOfBinTree LEAF = O
 NatOfBinTree (NODE x y) = 1+ (NatOfBinTree x)

 BinTreeSuc : BinTree -> BinTree
 BinTreeSuc x = NODE x LEAF

 BinTreePred : BinTree -> BinTree
 BinTreePred LEAF = LEAF
 BinTreePred (NODE x y) = x

 SMB : BinTree -> BinTree
 SMB x = NODE Smb x

 DBV : Nat -> BinTree
 DBV x = NODE Dbv (BinTreeOfNat x)

 DBL : BinTree -> BinTree
 DBL x = NODE Dbl x

 APL : BinTree -> BinTree -> BinTree
 APL x y = NODE Apl (NODE x y)

 LTS : BinTree -> BinTree -> BinTree
 LTS x y = NODE Lts (NODE x y)
 
 RED : BinTree -> BinTree
 RED x = NODE Red x

 RUL : BinTree -> BinTree
 RUL x = NODE Rul x

{-
 shift m (NODE x y) with x
 ... | Smb = NODE Smb y
 ... | Dbv = if (NatOfBinTree y) >= m then NODE Dbv (BinTreeSuc y) else NODE Dbv y

 shift m (NODE Dbv p) = if (NatOfBinTree p) >= m 
                        then (NODE Dbv (BinTreeSuc p))
                        else (NODE Dbv p)
 shift m (NODE Dbl x) = NODE Dbl (shift (1+ m) x)
 shift m x = x
-}
 
 shift : Nat -> BinTree -> BinTree 
-- shift m (NODE Smb x) = NODE Smb x
 shift m LEAF = LEAF
 shift m (NODE (NODE LEAF LEAF) x) = NODE (NODE LEAF LEAF) x
 shift m (NODE (NODE LEAF (NODE LEAF LEAF)) x) = if (NatOfBinTree x) >= m then NODE Dbv (BinTreeSuc x) else NODE Dbv x
 shift m (NODE (NODE LEAF (NODE (NODE LEAF LEAF) LEAF)) x) = NODE (NODE LEAF (NODE (NODE LEAF LEAF) LEAF)) (shift (1+ m) x)
 shift m (NODE (NODE LEAF (NODE LEAF (NODE LEAF LEAF))) (NODE x y)) = (NODE (NODE LEAF (NODE LEAF (NODE LEAF LEAF))) (NODE (shift m x) (shift m y)))
 shift m (NODE (NODE (NODE LEAF LEAF) (NODE LEAF (NODE LEAF LEAF))) (NODE x y)) = (NODE (NODE (NODE LEAF LEAF) (NODE LEAF (NODE LEAF LEAF))) (NODE (shift m x) (shift m y)))
 shift m (NODE (NODE (NODE LEAF LEAF) (NODE (NODE LEAF LEAF) LEAF)) x) = (NODE (NODE (NODE LEAF LEAF) (NODE (NODE LEAF LEAF) LEAF)) (shift m x))
 shift m (NODE (NODE (NODE LEAF LEAF) LEAF) x) = NODE (NODE (NODE LEAF LEAF) LEAF) x
 shift m (NODE x y) = NODE x y

-- variable substitution
 subst : Nat -> BinTree -> BinTree -> BinTree
 subst n (NODE (NODE LEAF (NODE LEAF LEAF)) p) x = if (NatOfBinTree p) == n then x else (if (NatOfBinTree p) >= (1+ n) then (NODE (NODE LEAF (NODE LEAF LEAF)) (BinTreePred p)) else (NODE (NODE LEAF (NODE LEAF LEAF)) p))
 subst n (NODE (NODE LEAF (NODE (NODE LEAF LEAF) LEAF)) x) y = (NODE (NODE LEAF (NODE (NODE LEAF LEAF) LEAF)) (subst (1+ n) x (shift O y)))
 subst n (NODE (NODE LEAF (NODE LEAF (NODE LEAF LEAF))) (NODE x y)) z = (NODE (NODE LEAF (NODE LEAF (NODE LEAF LEAF))) (NODE (subst n x z) (subst n y z)))
 subst n (NODE (NODE (NODE LEAF LEAF) (NODE LEAF (NODE LEAF LEAF))) (NODE x y)) z = (NODE (NODE (NODE LEAF LEAF) (NODE LEAF (NODE LEAF LEAF))) (NODE (subst n x z) (subst n y z)))
 subst n (NODE (NODE (NODE LEAF LEAF) (NODE (NODE LEAF LEAF) LEAF)) x) z = (NODE (NODE (NODE LEAF LEAF) (NODE (NODE LEAF LEAF) LEAF)) (subst n x z))
 subst n x y = x

-- reduction
 red1 : BinTree -> BinTree
 red1 (NODE (NODE LEAF (NODE (NODE LEAF LEAF) LEAF)) x) = NODE (NODE LEAF (NODE (NODE LEAF LEAF) LEAF)) (red1 x)
 red1 (NODE (NODE LEAF (NODE LEAF (NODE LEAF LEAF))) (NODE (NODE (NODE (NODE LEAF LEAF) LEAF) x) y)) = subst O x y
 red1 (NODE (NODE LEAF (NODE LEAF LEAF)) (NODE x y)) = (NODE (NODE LEAF (NODE LEAF LEAF)) (NODE (red1 x) (red1 y)))
 red1 (NODE (NODE (NODE LEAF LEAF) (NODE (NODE LEAF LEAF) LEAF)) (NODE x y)) = (NODE (NODE (NODE LEAF LEAF) (NODE (NODE LEAF LEAF) LEAF)) (NODE (red1 x) (red1 y)))
 red1 (NODE (NODE (NODE LEAF LEAF) (NODE (NODE LEAF LEAF) LEAF)) x) = (NODE (NODE (NODE LEAF LEAF) (NODE (NODE LEAF LEAF) LEAF)) (red1 x))
 red1 x = x

-- does a binary tree contain a symbol ? 
 _contSym_ : BinTree -> BinTree -> Bool
 (NODE (NODE LEAF LEAF) s) contSym s' = s === s'
 (NODE (NODE LEAF (NODE (NODE LEAF LEAF) LEAF)) x) contSym s = x contSym s
 (NODE (NODE LEAF (NODE LEAF (NODE LEAF LEAF))) (NODE x y)) contSym s = (x contSym s) or (y contSym s)
 (NODE (NODE (NODE LEAF LEAF) (NODE LEAF (NODE LEAF LEAF))) (NODE x y)) contSym s = (x contSym s) or (y contSym s)
 (NODE (NODE (NODE LEAF LEAF) (NODE (NODE LEAF LEAF) LEAF)) x) contSym s = x contSym s
 x contSym s = false

-- abstraction
 abstr : Nat -> BinTree -> BinTree -> BinTree
 abst : Nat -> BinTree -> BinTree -> BinTree
 abstr n s (NODE (NODE LEAF LEAF) x) = if s === x then (NODE (NODE LEAF (NODE LEAF LEAF)) (BinTreeOfNat n)) else (NODE (NODE LEAF LEAF) x)
 abstr n s (NODE (NODE LEAF (NODE (NODE LEAF LEAF) LEAF)) x) = (NODE (NODE LEAF (NODE (NODE LEAF LEAF) LEAF)) (abst (1+ n) s x))
 abstr n s (NODE (NODE LEAF (NODE LEAF (NODE LEAF LEAF))) (NODE x y)) = (NODE (NODE LEAF (NODE LEAF (NODE LEAF LEAF))) (NODE (abst n s x) (abst n s y)))
 abstr n s (NODE (NODE (NODE LEAF LEAF) (NODE LEAF (NODE LEAF LEAF))) (NODE x y)) = (NODE (NODE (NODE LEAF LEAF) (NODE LEAF (NODE LEAF LEAF))) (NODE (abst n s x) (abst n s y)))
 abstr n s (NODE (NODE (NODE LEAF LEAF) (NODE (NODE LEAF LEAF) LEAF)) x) = (NODE (NODE (NODE LEAF LEAF) (NODE (NODE LEAF LEAF) LEAF)) (abst n s x))
 abstr n s x = x
 abst n s x = if x contSym s then abstr n s x else x

 lambda : BinTree -> BinTree -> BinTree
 lambda x y = NODE Dbl (abst O x y)

 parent = NODE LEAF LEAF
 gparent = NODE LEAF (NODE LEAF LEAF)
 Allan = NODE (NODE LEAF LEAF) (NODE LEAF LEAF)
 Brenda = NODE (NODE LEAF LEAF) (NODE (NODE LEAF LEAF) LEAF)
 Charles = NODE (NODE LEAF LEAF) (NODE LEAF (NODE LEAF LEAF))
 x = NODE (NODE (NODE LEAF LEAF) LEAF) (NODE LEAF LEAF)
 y = NODE (NODE (NODE LEAF LEAF) LEAF) (NODE (NODE LEAF LEAF) LEAF)
 z = NODE (NODE (NODE LEAF LEAF) LEAF) (NODE LEAF (NODE LEAF LEAF))
 ruleGparent = (NODE (NODE (NODE LEAF LEAF) LEAF) LEAF)
 ruleAxiom1 = (NODE (NODE (NODE LEAF LEAF) LEAF) (NODE (NODE LEAF LEAF) LEAF))
 ruleAxiom2 = (NODE (NODE (NODE LEAF LEAF) LEAF) (NODE LEAF (NODE LEAF LEAF)))

-- side true p = x and side false p = y means p proves x = y
 side : Bool -> BinTree -> BinTree
 side s (NODE (NODE LEAF (NODE (NODE LEAF LEAF) LEAF)) x) = (NODE (NODE LEAF (NODE (NODE LEAF LEAF) LEAF)) (side s x))
 side s (NODE (NODE LEAF (NODE LEAF (NODE LEAF LEAF))) (NODE x y)) = (NODE (NODE LEAF (NODE LEAF (NODE LEAF LEAF))) (NODE (side s x) (side s y)))
 side s (NODE (NODE (NODE LEAF LEAF) (NODE (NODE LEAF LEAF) LEAF)) x) = (NODE (NODE (NODE LEAF LEAF) (NODE (NODE LEAF LEAF) LEAF)) (side s x))
 side s (NODE (NODE (NODE LEAF LEAF) (NODE LEAF (NODE LEAF LEAF))) (NODE x y)) = 
  if (side true x) === (side true y)
  then (if s then side false x else side false y)
  else (NODE (NODE (NODE LEAF LEAF) (NODE (NODE LEAF LEAF) LEAF)) x)
 side s (NODE (NODE (NODE LEAF LEAF) LEAF) LEAF) = if s 
  then lambda x (lambda y (lambda z (APL (APL (APL (SMB parent) (SMB x)) (SMB y)) (APL (APL (APL (SMB parent) (SMB y)) (SMB z)) (APL (APL (SMB gparent) (SMB x)) (SMB z))))))
  else lambda x (lambda y (lambda z (DBL (DBV O))))
 side s (NODE (NODE (NODE LEAF LEAF) LEAF) (NODE (NODE LEAF LEAF) LEAF)) = if s
  then APL (APL (SMB parent) (SMB Allan)) (SMB Brenda)
  else DBL (DBV O)
 side s (NODE (NODE (NODE LEAF LEAF) LEAF) (NODE LEAF (NODE LEAF LEAF))) = if s
  then APL (APL (SMB parent) (SMB Brenda)) (SMB Charles)
  else DBL (DBV O)
 side _ x = x

 develop : BinTree -> ProvedEq
 develop p = p proves side true p equals side false p

-- example of proof

 lemma1 = RED (APL (APL (APL ruleGparent (SMB Allan)) (SMB Brenda)) (SMB Charles))
 lemma2 = RED (APL ruleAxiom1 (APL (APL (APL (SMB parent) (SMB Brenda)) (SMB Charles)) (APL (APL (SMB gparent) (SMB Allan)) (SMB Charles))))
 lemma3 = LTS lemma2 lemma1
 lemma4 = RED (APL ruleAxiom2 (APL (APL (SMB gparent) (SMB Allan)) (SMB Charles)))
 theorem1 = LTS lemma4 lemma3
