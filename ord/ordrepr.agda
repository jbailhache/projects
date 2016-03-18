module ordrepr where

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

 not : Bool -> Bool
 not true = false
 not false = true

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

 limn : (n : Nat) -> (Nat -> ford n) -> ford n
 limn O f = Lim f
 limn (1+ p) f = \x -> limn p (\n -> f n x)

 Subst : Ord -> (Ord -> Ord) -> Ord -> Ord 
 Subst Zero s z = z
 Subst (Suc x) s z = s (Subst x s z)
 Subst (Lim f) s z = Lim (\n -> Subst (f n) s z)

 Substn : {n : Nat} -> Ord -> ford (1+ (1+ n))
 Substn Zero s z = z
 Substn (Suc x) s z = s (Substn x s z)
 Substn (Lim f) s z = limn _ (\n -> Substn (f n) s z)

 
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

 var : String -> Proof
 var v = SMB v

 APL2 : Proof -> Proof -> Proof -> Proof
 APL2 f x y = APL (APL f x) y

 APL3 : Proof -> Proof -> Proof -> Proof -> Proof
 APL3 f x y z = APL (APL (APL f x) y) z

 APL4 : Proof -> Proof -> Proof -> Proof -> Proof -> Proof
 APL4 f x1 x2 x3 x4 = APL (APL (APL (APL f x1) x2) x3) x4

 APL5 : Proof -> Proof -> Proof -> Proof -> Proof -> Proof -> Proof
 APL5 f x1 x2 x3 x4 x5 = APL (APL (APL (APL (APL f x1) x2) x3) x4) x5

 APL6 : Proof -> Proof -> Proof -> Proof -> Proof -> Proof -> Proof -> Proof
 APL6 f x1 x2 x3 x4 x5 x6 = APL (APL (APL (APL (APL (APL f x1) x2) x3) x4) x5) x6

 APL7 : Proof -> Proof -> Proof -> Proof -> Proof -> Proof -> Proof -> Proof -> Proof
 APL7 f x1 x2 x3 x4 x5 x6 x7 = APL (APL (APL (APL (APL (APL (APL f x1) x2) x3) x4) x5) x6) x7

-- Combinators

 P_I = lambda "a" (var "a")
 P_K = lambda "a" (lambda "b" (var "b"))
 P_S = lambda "a" (lambda "b" (lambda "c" (APL (APL (var "a") (var "c")) (APL (var "b") (var "c")))))
 P_KI = (lambda "a" (lambda "b" (var "b")))
 P_CI = lambda "a" (lambda "b" (APL (var "b") (var "a")))
 P_P = (lambda "a" (lambda "b" (lambda "c" (APL (APL (var "c") (var "a")) (var "b")))))
 P_A1 = P_CI
 P_A2 = P_P
 P_A3 = lambda "a1" (lambda "a2" (lambda "a3" (lambda "f" (APL (APL (APL (var "f") (var "a1")) (var "a2")) (var "a3")))))
 P_A4 = lambda "a1" (lambda "a2" (lambda "a3" (lambda "a4" (lambda "f" (APL (APL (APL (APL (var "f") (var "a1")) (var "a2")) (var "a3")) (var "a4")) ))))
 P_B = (lambda "f" (lambda "g" (lambda "x" (APL (var "f") (APL (var "g") (var "x"))))))
 P_A = (lambda "x" (APL (var "x") (var "x")))
 P_Y = (lambda "f" (APL P_A (APL (APL P_B (var "f")) P_A)))

 P_zero = P_K
 P_suc = (lambda "n" (lambda "z" (lambda "s" (APL (var "s") (var "n")))))
 P0 = P_zero
 P1 = APL P_suc P0
 P2 = APL P_suc P1
 P3 = APL P_suc P2
 P4 = APL P_suc P3
 P5 = APL P_suc P4

 P_Zero = (lambda "z" (lambda "s" (lambda "l" (var "z"))))
 P_Suc = (lambda "x" (lambda "z" (lambda "s" (lambda "l" (APL (var "s") (var "x"))))))
 P_Lim = (lambda "f" (lambda "z" (lambda "s" (lambda "l" (APL (var "l") (var "f"))))))
 insert = lambda "x" (lambda "l" (lambda "f" (APL (var "l") (APL (var "f") (var "x")))))
 array = APL P_Y (lambda "array" (lambda "f" (lambda "n" (lambda "x" (APL2 (var "n") (APL (var "f") P_I) (lambda "p" (APL2 (var "array") (lambda "l" (APL (var "f") (APL2 insert (var "x") (var "l")))) (var "n"))))))))

 polt : Proof -> Proof
 polt x = x

 ltop : Proof -> Proof
 ltop x = x

-- Representations

 P_RAXM = lambda "AXM" (lambda "smb" (lambda "db0" (lambda "dbs" (lambda "dbl" (lambda "APL" (lambda "ltr" (var "AXM")))))))
 P_RSMB = lambda "AXM" (lambda "smb" (lambda "db0" (lambda "dbs" (lambda "dbl" (lambda "APL" (lambda "ltr" (var "smb")))))))
 P_RDB0 = lambda "AXM" (lambda "smb" (lambda "db0" (lambda "dbs" (lambda "dbl" (lambda "APL" (lambda "ltr" (var "db0")))))))
 P_RDBS = lambda "x" (lambda "AXM" (lambda "smb" (lambda "db0" (lambda "dbs" (lambda "dbl" (lambda "APL" (lambda "ltr" (APL (var "dbs") (var "x")))))))))
 P_RDBL = lambda "x" (lambda "AXM" (lambda "smb" (lambda "db0" (lambda "dbs" (lambda "dbl" (lambda "APL" (lambda "ltr" (APL (var "dbl") (var "x")))))))))
 P_RAPL = lambda "x" (lambda "y" (lambda "AXM" (lambda "smb" (lambda "db0" (lambda "dbs" (lambda "dbl" (lambda "APL" (lambda "ltr" (APL (APL (var "APL") (var "x")) (var "y"))))))))))
 P_RLTR = lambda "x" (lambda "y" (lambda "AXM" (lambda "smb" (lambda "db0" (lambda "dbs" (lambda "dbl" (lambda "APL" (lambda "ltr" (APL (APL (var "ltr") (var "x")) (var "y"))))))))))

 rep : Proof -> Proof
 rep AXM = polt P_RAXM
 rep (SMB _) = polt P_RSMB
 rep DB0 = polt P_RDB0
 rep (DBS x) = APL (polt P_RDBS) (rep x)
 rep (DBL x) = APL (polt P_RDBL) (rep x)
 rep (APL x y) = APL (APL (polt P_RAPL) (rep x)) (rep y)
 rep (LTR x y) = APL (APL (polt P_RLTR) (rep x)) (rep y) 

 repLT : Proof -> Proof
 repLT x = ltop (rep (polt x))

 P_equal = APL P_Y (lambda "equal" (lambda "x" (lambda "y"
  (APL (APL (APL (APL (APL (APL (APL (var "x")
   (APL (APL (APL (APL (APL (APL (APL (var "y") P_K) P_KI) P_KI) (APL P_K P_KI)) (APL P_K P_KI)) (APL P_K (APL P_K P_KI))) (APL P_K (APL P_K P_KI))) )
   (APL (APL (APL (APL (APL (APL (APL (var "y") P_KI) P_K) P_KI) (APL P_K P_KI)) (APL P_K P_KI)) (APL P_K (APL P_K P_KI))) (APL P_K (APL P_K P_KI))) )
   (APL (APL (APL (APL (APL (APL (APL (var "y") P_KI) P_KI) P_K) (APL P_K P_KI)) (APL P_K P_KI)) (APL P_K (APL P_K P_KI))) (APL P_K (APL P_K P_KI))) )
   (lambda "a" (APL (APL (APL (APL (APL (APL (APL (var "y") P_KI) P_KI) P_KI) (APL (var "equal") (var "a"))) (APL P_K P_KI)) (APL P_K (APL P_K P_KI))) (APL P_K (APL P_K P_KI))) ) )
   (lambda "a" (APL (APL (APL (APL (APL (APL (APL (var "y") P_KI) P_KI) P_KI) (APL P_K P_KI)) (APL (var "equal") (var "a"))) (APL P_K (APL P_K P_KI))) (APL P_K (APL P_K P_KI))) ) )
   (lambda "x1" (lambda "x2" (APL (APL (APL (APL (APL (APL (APL (var "y") P_KI) P_KI) P_KI) (APL P_K P_KI)) (APL P_K P_KI)) 
    (lambda "y1" (lambda "y2" (APL (APL (APL (APL (var "equal") (var "x1")) (var "y1")) (APL (APL (var "equal")(var "x2")) (var "y2"))) P_KI)))
     ) (APL P_K (APL P_K P_KI))) )) )
   (lambda "x1" (lambda "x2" (APL (APL (APL (APL (APL (APL (APL (var "y") P_KI) P_KI) P_KI) (APL P_K P_KI)) (APL P_K P_KI)) (APL P_K (APL P_K P_KI)))
    (lambda "y1" (lambda "y2" (APL (APL (APL (APL (var "equal") (var "x1")) (var "y1")) (APL (APL (var "equal")(var "x2")) (var "y2"))) P_KI)))
     )  )) )
  )))

 P_shift = APL P_Y (lambda "shift" (lambda "u" (lambda "x" 
  (APL (APL (APL (APL (var "equal") (var "x")) (var "u")) (APL P_RDBS (var "u")))
   (APL (APL (APL (APL (APL (APL (APL (var "x")
    P_RAXM )
    P_RSMB )
    P_RDB0 )
    (lambda "x1" (APL P_RDBS (APL (APL (var "shift") (var "u")) (var "x1")))) )
    (lambda "x1" (APL P_RDBL (APL (APL (var "shift") (APL P_RDBS (var "u"))) (var "x1")))) )
    (lambda "x1" (lambda "x2" (APL (APL P_RAPL 
      (APL (APL (var "shift") (var "u")) (var "x1")) )
      (APL (APL (var "shift") (var "u")) (var "x2")) ) )) )
    (lambda "x1" (lambda "x2" (APL (APL P_RLTR 
      (APL (APL (var "shift") (var "u")) (var "x1")) )
      (APL (APL (var "shift") (var "u")) (var "x2")) ) )) )
   ))))
    
 P_subst = APL P_Y (lambda "subst" (lambda "u" (lambda "a" (lambda "b"
  (APL (APL (APL (APL P_equal (var "a")) (var "u")) (var "b"))
   (APL (APL (APL (APL (APL (APL (APL (var "a")
    P_RAXM )
    P_RSMB )
    P_RDB0 )
    (lambda "a1" (APL (APL (APL (APL P_equal (var "a1")) (var "u")) (var "u")) (APL P_RDBS (APL (APL (APL (var "subst") (var "u")) (var "a1")) (var "b"))))) )
    (lambda "a1" (APL P_RDBL (APL (APL (APL (var "subst") (APL P_RDBS (var "u"))) (var "a1")) (APL (APL P_shift P_RDB0) (var "b"))))) )
    (lambda "a1" (lambda "a2" (APL (APL P_RAPL (APL (APL (APL (var "subst") (var "u")) (var "a1")) (var "b"))) (APL (APL (APL (var "subst") (var "u")) (var "a2")) (var "b"))))) )
    (lambda "a1" (lambda "a2" (APL (APL P_RLTR (APL (APL (APL (var "subst") (var "u")) (var "a1")) (var "b"))) (APL (APL (APL (var "subst") (var "u")) (var "a2")) (var "b"))))))
   )))))

 P_red1 = APL P_Y (lambda "red1" (lambda "x" 
  (APL (APL (APL (APL (APL (APL (APL (var "x")
   P_RAXM )
   P_RSMB )
   P_RDB0 )
   (lambda "x1" (APL P_RDBS (APL (var "red1") (var "x1")))) )
   (lambda "x1" (APL P_RDBL (APL (var "red1") (var "x1")))) )
   (lambda "x1" (lambda "x2" (APL (APL (APL (APL (APL (APL (APL (var "x1")
    (APL (APL P_RAPL (APL (var "red1") (var "x1"))) (APL (var "red1") (var "x2"))) )
    (APL (APL P_RAPL (APL (var "red1") (var "x1"))) (APL (var "red1") (var "x2"))) )
    (APL (APL P_RAPL (APL (var "red1") (var "x1"))) (APL (var "red1") (var "x2"))) )
    (APL P_K (APL (APL P_RAPL (APL (var "red1") (var "x1"))) (APL (var "red1") (var "x2")))) )
    (lambda "x3" (APL (APL (APL P_subst P_RDB0) (var "x3")) (var "x2"))) )
    (APL P_K (APL P_K (APL (APL P_RAPL (APL (var "red1") (var "x1"))) (APL (var "red1") (var "x2"))))) )
    (APL P_K (APL P_K (APL (APL P_RAPL (APL (var "red1") (var "x1"))) (APL (var "red1") (var "x2"))))) )
    )) )
   (lambda "x1" (lambda "x2" (APL (APL P_RLTR (APL (var "red1") (var "x1"))) (APL (var "red1") (var "x2")) ))) )
  ))

 P_red = APL P_Y (lambda "red" (lambda "x"
  (APL (lambda "y" (APL (APL (APL (APL P_equal (var "x")) (var "y")) (var "x")) (APL (var "red") (var "y")))) (APL P_red1 (var "x"))) ))

 P_side = APL P_Y (lambda "side" (lambda "t" (lambda "s" (lambda "x"
  (APL (APL (APL (APL (APL (APL (APL (var "x")
   -- (APL (APL (var "s") (APL (var "t") P_K)) (APL (var "t") P_KI)) )
   (APL (APL (var "s") (APL (APL P_RAPL (var "t")) (repLT P_K))) (APL (APL P_RAPL (var "t")) (repLT P_KI))) )
   -- (APL (var "t") (var "s")) )
   P_RSMB )
   P_RDB0 )
   (lambda "x1" (APL P_RDBS (APL (APL (APL (var "side") (var "t")) (var "s")) (var "x1")))) )
   (lambda "x1" (APL P_RDBL (APL (APL (APL (var "side") (var "t")) (var "s")) (var "x1")))) )
   (lambda "x1" (lambda "x2" (APL (APL P_RAPL (APL (APL (APL (var "side") (var "t")) (var "s")) (var "x1"))) (APL (APL (APL (var "side") (var "t")) (var "s")) (var "x2"))))) )
   (lambda "x1" (lambda "x2" 
    (APL (APL (APL (APL (var "equal") (APL (var "red") (APL (APL (APL (var "side") (var "t")) P_K) (var "x1")))) (APL (var "red") (APL (APL (APL (var "side") (var "t")) P_K) (var "x2"))))
    (APL P_red (APL (APL (APL (var "side") (var "t")) P_KI) (APL (APL (var "s") (var "x1")) (var "x2")))) )
    (APL (APL P_RLTR (var "x1")) (var "x2")) ) )) ) 
   ))))

 P_eval = APL P_Y (lambda "eval" (lambda "x"
  (APL (APL (APL (APL (APL (APL (APL (var "x")
    AXM )
    (SMB "SMB") )
    DB0 )
    (lambda "x1" (DBS (APL (var "eval") (var "x1")))) )
    (lambda "x1" (DBL (APL (var "eval") (var "x1")))) )
    (lambda "x1" (lambda "x2" (APL (APL (var "eval") (var "x1")) (APL (var "eval") (var "x2"))))) )
    (lambda "x1" (lambda "x2" (LTR (APL (var "eval") (var "x1")) (APL (var "eval") (var "x2"))))) )
  ))

{-
 P_Subst {ZERO} s z = z
 P_Subst {APL SUC x} s z = APL s (P_Subst {x} s z)
 P_Subst {H f x} = APL2 H (P_Subst {f} s z) (P_Subst {x} s z)
-}
 P_Subst = APL P_Y (lambda "P_Subst" (lambda "x" (lambda "s" (lambda "z"
  (APL3 (var "x")
   (var "z")
   (lambda "y" (APL (var "s") (APL3 (var "P_Subst") (var "y") (var "s") (var "z"))))
   (lambda "f" (APL P_Lim (lambda "n" (APL3 (var "P_Subst") (APL (var "f") (var "n")) (var "s") (var "z"))))) ) ))))

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
 -- nthAPL n (DBL x) y = APL (DBL (nth n x)) (nth n y)
 nthAPL n (DBL x) y = if (nth n x) === x then APL (DBL x) (nth n y) else APL (DBL (nth n x)) y
 nthAPL n (LTR x1 x2) y = APL (LTR (nth n x1) (nth n x2)) (nth n y)
 nthAPL n (APL x1 x2) y = nthAPL2 n x1 x2 y 
 nthAPL2 n AXM y z = if nth n y === y then APL (APL AXM y) (nth n z) else APL (APL AXM (nth n y)) z
 nthAPL2 n DB0 y z = if nth n y === y then APL (APL DB0 y) (nth n z) else APL (APL DB0 (nth n y)) z
 nthAPL2 n (DBS x) y z = if nth n y === y then APL (APL (DBS x) y) (nth n z) else APL (APL (DBS x) (nth n y)) z
 nthAPL2 n (DBL x) y z = 
  if not (nth n x === y) then APL (APL (DBL (nth n x)) y) z else
  if not (nth n y === y) then APL (APL (DBL x) (nth n y)) z else
                              APL (APL (DBL x) y) (nth n z)
 nthAPL2 n (LTR x1 x2) y z = APL (APL (LTR (nth n x1) (nth n x2)) (nth n y)) (nth n z)
 nthAPL2 n (APL x1 x2) y z = 
  if not (nth n x1 === x1) then APL (APL (APL (nth n x1) x2) y) z else
  if not (nth n x2 === x2) then APL (APL (APL x1 (nth n x2)) y) z else
  if not (nth n y === y)   then APL (APL (APL x1 x2) (nth n y)) z else
                                APL (APL (APL x1 x2) y) (nth n z)
 nthAPL2 n (SMB s) y z = 
  if (s eq "H") then (repeat n y z) else 
  if not (nth n y === y) then APL (APL (SMB s) (nth n y)) z else
                              APL (APL (SMB s) y) (nth n z)

{-
 nthAPL2 n AXM y z = APL (APL AXM (nth n y)) (nth n z)
 nthAPL2 n DB0 y z = APL (APL DB0 (nth n y)) (nth n z)
 nthAPL2 n (DBS x) y z = APL (APL (DBS x) (nth n y)) (nth n z)
 nthAPL2 n (DBL x) y z = APL (APL (DBL (nth n x)) (nth n y)) (nth n z)
 nthAPL2 n (LTR x1 x2) y z = APL (APL (LTR (nth n x1) (nth n x2)) (nth n y)) (nth n z)
 nthAPL2 n (APL x1 x2) y z = APL (APL (APL (nth n x1) (nth n x2)) (nth n y)) (nth n z)
 nthAPL2 n (SMB s) y z = if (s eq "H") then (repeat n y z) else (APL (APL (SMB s) (nth n y)) (nth n z))
-}

 
 OrdOfRepN : Nat -> Proof -> Ord
 OrdOfRep1 : Nat -> Proof -> Ord
 OrdOfRepApl : Nat -> Proof -> Proof -> Ord
 OrdOfRepN O x = Zero
 OrdOfRepN (1+ n) x = OrdOfRep1 n (red x)
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

{-
 ZERO = SMB "Zero"
 SUC = SMB "Suc"
 H = SMB "H"
-}
 
 ZERO = APL (SMB "SMB") P0
 SUC = APL (SMB "SMB") P1
 H = APL (SMB "SMB") P2


 w = APL2 H SUC ZERO
 w**w = APL3 H H SUC ZERO

 R1 = lambda "f" (APL2 H (APL P_CI (var "f")) P_I)
 epsilon0 = APL3 R1 H SUC ZERO

 R2 = lambda "f1" (lambda "f2" (APL2 H (APL2 P_P (var "f1") (var "f2")) P_I))
 zeta0 = APL4 R2 R1 H SUC ZERO
 
 R3 = lambda "f1" (lambda "f2" (lambda "f3" (APL2 H (APL3 P_A3 (var "f1") (var "f2") (var "f3")) P_I)))
 phi30 = APL5 R3 R2 R1 H SUC ZERO

 R4 = lambda "f1" (lambda "f2" (lambda "f3" (lambda "f4" (APL2 H (APL4 P_A4 (var "f1") (var "f2") (var "f3") (var "f4")) P_I))))

 R = APL array (lambda "l" (APL2 H (var "l") P_I))
 phi30' = APL5 (APL R (APL P_suc (APL P_suc (APL P_suc P_zero)))) (APL R (APL P_suc (APL P_suc P_zero))) (APL R (APL P_suc P_zero)) H SUC ZERO

 ARN = APL P_Y (lambda "ARN" (lambda "n" (APL2 (var "n") 
  P_I 
  (lambda "p" (APL2 insert (APL R (APL P_suc (var "n"))) (APL (var "ARN") (var "p"))))
  )))
 phi30'' = APL5 ARN (APL P_suc (APL P_suc (APL P_suc P_zero))) P_I H SUC ZERO

{-
 ARO = APL P_Y (lambda "ARO" (lambda "x" (APL3 (var "x")
  P_I
  (lambda "p" (APL2 insert (APL R (APL P_suc (var "n"))) (APL (var "ARO") (var "p"))))
  (lambda "f" (LIM (lambda "n" (APL (var "ARO") (var "n"))))
  )))
-}

 phiw0 = APL5 ARN (APL2 H P_suc P_zero) P_I H SUC ZERO
 Rwt1HS0 = APL5 ARN (APL2 H P_suc P_zero) P_I H SUC ZERO
 Rw+1t1HS0 = APL4 R2 (APL2 ARN (APL2 H P_suc P_zero) P_I) H SUC ZERO
 Rwt1 = APL2 ARN (APL2 H P_suc P_zero) P_I
 Rwt1HS0' = APL3 Rwt1 H SUC ZERO
 Rw+1t1HS0' = APL4 R2 Rwt1 H SUC ZERO
 Rw+2t1HS0 = APL5 R3 R2 Rwt1 H SUC ZERO
 Rw+3t1HS0 = APL6 R4 R3 R2 Rwt1 H SUC ZERO

{-
 ARNN = APL P_Y (lambda "ARNN" (lambda "n" (lambda "p" (APL2 (var "n")
  P_I
  (lambda "n1" (APL2 insert (APL R (var "p")) (APL2 (var "ARNN") (var "n1") (APL2 (var "p") P_zero P_I))))
  ))))
 phi30''' = APL6 ARNN (APL P_suc (APL P_suc (APL P_suc P_zero))) (APL P_suc (APL P_suc (APL P_suc P_zero))) P_I H SUC ZERO 
-}

 lt = APL P_Y (lambda "lt" (lambda "n" (lambda "p" (APL2 (var "n") P_K (lambda "n1" (APL2 (var "p") P_KI (lambda "p1" (APL2 (var "lt") (var "n1") (var "p1")))))))))

 ARNN = APL P_Y (lambda "ARNN" (lambda "n" (lambda "p" 
  (APL2 (var "n")
   P_I
   (lambda "n1"
    (APL2 (APL2 lt (APL P_suc (APL P_suc (var "n1"))) (var "p"))
     P_I
     (APL2 insert (APL R (APL P_suc (var "n"))) (APL2 (var "ARNN") (var "n1") (var "p"))) ) ) ) )))

 Rw+3t1HS0' = APL7 ARNN P4 P2 P_I Rwt1 H SUC ZERO

 Rwt1' = APL3 ARNN (APL2 H P_suc P_zero) P1 P_I
 Rwt2 = APL3 ARNN (APL2 H P_suc P_zero) P2 P_I
 Rw*2t1HS0 = APL4 Rwt2 Rwt1' H SUC ZERO
 Rw*2t1HS0' = APL4 (APL3 ARNN (APL2 H P_suc P_zero) P2 P_I) (APL3 ARNN (APL2 H P_suc P_zero) P1 P_I) H SUC ZERO

 ARw*n = APL P_Y (lambda "ARw*n" (lambda "n" (APL2 (var "n")
          P_zero
          (lambda "p" (APL2 insert (APL3 ARNN (APL2 H P_suc P_zero) (var "p") P_I) 
                                   (APL (var "ARw*n") (var "p")) )) )))
 Rw*2t1HS0'' = APL5 ARw*n P2 P_I H SUC ZERO
 Rw*wt1HS0 = APL6 ARw*n (APL2 H P_suc P_zero) P_I H SUC ZERO


 R0 = APL2 P_P P_zero P_I

 Rsuc = lambda "x" (APL2 P_P (APL P_suc (APL (var "x") P_K)) (APL2 insert (APL R (APL P_suc (APL (var "x") P_K))) (APL (var "x") P_KI)))

 w' = APL4 R0 P_KI P_I SUC ZERO
 epsilon0' = APL4 (APL Rsuc R0) P_KI P_I SUC ZERO
 zeta0' = APL4 (APL Rsuc (APL Rsuc R0)) P_KI P_I SUC ZERO
 Rwt1HS0'' = APL4 (APL2 H Rsuc R0) P_KI P_I SUC ZERO
 Rw+1t1HS0'' = APL4 (APL Rsuc (APL2 H Rsuc R0)) P_KI P_I SUC ZERO

 -- Rx->1 H SUC ZERO = [ SUC -> Rsuc, ZERO -> R0 ] x P_KI P_I SUC ZERO

{-
 Rxt1HS0 : Proof -> Proof
 -- Rxt1HS0 x = APL4 (Subst (OrdOfRep x) (APL Rsuc) R0) P_KI P_I SUC ZERO
 -- problem : (APL Rsuc is Proof -> Proof, should be Ord -> Ord

 Rxt1HS0 : Proof
 Rxt1HS0 = lambda "x" (APL4 (Subst (OrdOfRep (var "x")) (APL Rsuc) R0) P_KI P_I SUC ZERO)
-}

 -- Rxt1HS0R = lambda "x" ({APL4} (P_Subst (var "x") {APL R_suc} {R0}) {P_KI} {P_I} SUC ZERO

 Rxt1HS0R = lambda "x" (APL2 P_RAPL (APL2 P_RAPL (APL2 P_RAPL (APL2 P_RAPL 
  (APL2 P_RAPL (APL2 P_RAPL (APL2 P_RAPL P_Subst (var "x")) (APL P_RAPL (rep P_suc))) (rep R0))
  (rep P_KI) )
  (rep P_I) )
  SUC )
  ZERO )




