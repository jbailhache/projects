module sslc_tirp where

{-
 theory with 1 axiom a = b represented by t = < a , b > = P a b = \f . f a b
 proof AXM
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
 red1 (APL x y) = APL (red1 x) (red1 y)
 red1 (LTR x y) = LTR (red1 x) (red1 y)

 redn : Nat -> Proof -> Proof
 redn O x = x
 redn (1+ n) x = if (red1 x) === x then x else redn n (red1 x)

 red : Proof -> Proof
 red a = redn 10000 a

{-
 side : Bool -> Proof -> Proof -> Proof -> Proof
 side s a b AXM = if s then a else b
 side _ _ _ SMB = SMB
 side _ _ _ DB0 = DB0
 side _ _ _ (DBS x) = DBS x
 side s a b (DBL x) = DBL (side s a b x)
 side s a b (APL x y) = APL (side s a b x) (side s a b y)
 side s a b (LTR x y) = if red (side true a b x) === red (side true a b y) then (if s then red (side false a b x) else red (side false a b y)) else (LTR x y)

 -- side s a b (LTR x y) = if red (side true a b x) === red (side true a b y) then red (side false a b (if s then x else y)) else (LTR x y)
-}

 side : Proof -> Bool -> Proof -> Proof
 -- side : (Bool -> Proof) -> Bool -> Proof -> Proof
 side t s AXM = if s then (APL t (DBL (DBL (DBS DB0)))) else (APL t (DBL (DBL DB0)))
 -- side t s AXM = t s
 side _ _ SMB = SMB
 side _ _ DB0 = DB0
 side _ _ (DBS x) = DBS x
 side t s (DBL x) = DBL (side t s x)
 side t s (APL x y) = APL (side t s x) (side t s y)
 side t s (LTR x y) = if red (side t true x) === red (side t true y) then (if s then red (side t false x) else red (side t false y)) else (LTR x y)

 -- example of theory : SMB = (APL SMB SMB)
 t1 = DBL (APL (APL DB0 SMB) (APL SMB SMB))

 P_K = DBL (DBL (DBS DB0))
 P_KI = DBL (DBL DB0)

 -- red (APL t1 P_K) = SMB
 -- red (APL t1 P_KI) = APL SMB SMB
 -- red (side t1 true AXM) = SMB
 -- red (side t1 false AXM) = APL SMB SMB

 data LambdaTerm : Set where
  axm : LambdaTerm
  smb : LambdaTerm
  db0 : LambdaTerm
  dbs : LambdaTerm -> LambdaTerm
  dbl : LambdaTerm -> LambdaTerm
  apl : LambdaTerm -> LambdaTerm -> LambdaTerm
  ltr : LambdaTerm -> LambdaTerm -> LambdaTerm
  var : String -> LambdaTerm
  lbd : String -> LambdaTerm -> LambdaTerm

 _contVar_ : LambdaTerm -> String -> Bool
 axm contVar _ = false
 smb contVar _ = false
 db0 contVar _ = false
 -- (dbs _) contVar _ = false
 (dbs x) contVar v = x contVar v
 (dbl x) contVar v = x contVar v
 (apl x y) contVar v = (x contVar v) or (y contVar v)
 (ltr x y) contVar v = (x contVar v) or (y contVar v)
 (var u) contVar v = u eq v
 (lbd u x) contVar v = x contVar v

 abstr : LambdaTerm -> String -> LambdaTerm -> LambdaTerm
 abst : LambdaTerm -> String -> LambdaTerm -> LambdaTerm
 abst d v x = if (x contVar v) then (abstr d v x) else x
 -- abst d v x = abstr d v x
 abstr _ _ axm = axm
 abstr _ _ smb = smb
 abstr _ _ db0 = db0
 abstr d v (dbs x) = dbs (abst d v x)
 abstr d v (dbl x) = dbl (abst (dbs d) v x) 
 abstr d v (apl x y) = apl (abst d v x) (abst d v y)
 abstr d v (ltr x y) = ltr (abst d v x) (abst d v y)
 abstr d v (var u) = if v eq u then d else (var u)
 abstr d v (lbd u x) = lbd v (abst d u x)

 LambdaTermOfProof : Proof -> LambdaTerm
 LambdaTermOfProof AXM = axm
 LambdaTermOfProof SMB = smb
 LambdaTermOfProof DB0 = db0
 LambdaTermOfProof (DBS x) = dbs (LambdaTermOfProof x)
 LambdaTermOfProof (DBL x) = dbl (LambdaTermOfProof x)
 LambdaTermOfProof (APL x y) = apl (LambdaTermOfProof x) (LambdaTermOfProof y)
 LambdaTermOfProof (LTR x y) = ltr (LambdaTermOfProof x) (LambdaTermOfProof y)

 ltop : Proof -> LambdaTerm
 ltop x = LambdaTermOfProof x

 ProofOfLambdaTerm : LambdaTerm -> Proof
 ProofOfLambdaTerm axm = AXM
 ProofOfLambdaTerm smb = SMB
 ProofOfLambdaTerm db0 = DB0
 ProofOfLambdaTerm (dbs x) = DBS (ProofOfLambdaTerm x)
 ProofOfLambdaTerm (dbl x) = DBL (ProofOfLambdaTerm x)
 ProofOfLambdaTerm (apl x y) = APL (ProofOfLambdaTerm x) (ProofOfLambdaTerm y)
 ProofOfLambdaTerm (ltr x y) = LTR (ProofOfLambdaTerm x) (ProofOfLambdaTerm y)
 ProofOfLambdaTerm (var s) = SMB
 ProofOfLambdaTerm (lbd s x) = SMB

 polt : LambdaTerm -> Proof
 polt x = ProofOfLambdaTerm x

 lambda : String -> LambdaTerm -> LambdaTerm
 lambda v x = dbl (abst db0 v x)

-- Combinators

 LT_I = (lambda "a" (var "a"))
 LT_K = (lambda "a" (lambda "b" (var "b")))
 LT_S = (lambda "a" (lambda "b" (lambda "c" (apl (apl (var "a") (var "c")) (apl (var "b") (var "c"))))))
 LT_KI = (lambda "a" (lambda "b" (var "b")))
 LT_P = (lambda "a" (lambda "b" (lambda "c" (apl (apl (var "c") (var "a")) (var "b")))))
 LT_B = (lambda "f" (lambda "g" (lambda "x" (apl (var "f") (apl (var "g") (var "x"))))))
 LT_A = (lambda "x" (apl (var "x") (var "x")))
 LT_Y = (lambda "f" (apl LT_A (apl (apl LT_B (var "f")) LT_A)))
 LT_zero = LT_K
 LT_suc = (lambda "n" (lambda "z" (lambda "s" (apl (var "s") (var "n")))))
 LT_Zero = (lambda "z" (lambda "s" (lambda "l" (var "z"))))
 LT_Suc = (lambda "x" (lambda "z" (lambda "s" (lambda "l" (apl (var "s") (var "x"))))))
 LT_Lim = (lambda "f" (lambda "z" (lambda "s" (lambda "l" (apl (var "l") (var "f"))))))
 
-- Representations

 LT_RAXM = lambda "axm" (lambda "smb" (lambda "db0" (lambda "dbs" (lambda "dbl" (lambda "apl" (lambda "ltr" (var "axm")))))))
 LT_RSMB = lambda "axm" (lambda "smb" (lambda "db0" (lambda "dbs" (lambda "dbl" (lambda "apl" (lambda "ltr" (var "smb")))))))
 LT_RDB0 = lambda "axm" (lambda "smb" (lambda "db0" (lambda "dbs" (lambda "dbl" (lambda "apl" (lambda "ltr" (var "db0")))))))
 LT_RDBS = lambda "x" (lambda "axm" (lambda "smb" (lambda "db0" (lambda "dbs" (lambda "dbl" (lambda "apl" (lambda "ltr" (apl (var "dbs") (var "x")))))))))
 LT_RDBL = lambda "x" (lambda "axm" (lambda "smb" (lambda "db0" (lambda "dbs" (lambda "dbl" (lambda "apl" (lambda "ltr" (apl (var "dbl") (var "x")))))))))
 LT_RAPL = lambda "x" (lambda "y" (lambda "axm" (lambda "smb" (lambda "db0" (lambda "dbs" (lambda "dbl" (lambda "apl" (lambda "ltr" (apl (apl (var "apl") (var "x")) (var "y"))))))))))
 LT_RLTR = lambda "x" (lambda "y" (lambda "axm" (lambda "smb" (lambda "db0" (lambda "dbs" (lambda "dbl" (lambda "apl" (lambda "ltr" (apl (apl (var "ltr") (var "x")) (var "y"))))))))))

 rep : Proof -> Proof
 rep AXM = polt LT_RAXM
 rep SMB = polt LT_RSMB
 rep DB0 = polt LT_RDB0
 rep (DBS x) = APL (polt LT_RDBS) (rep x)
 rep (DBL x) = APL (polt LT_RDBL) (rep x)
 rep (APL x y) = APL (APL (polt LT_RAPL) (rep x)) (rep y)
 rep (LTR x y) = APL (APL (polt LT_RLTR) (rep x)) (rep y) 

 repLT : LambdaTerm -> LambdaTerm
 repLT x = ltop (rep (polt x))

 LT_equal = apl LT_Y (lambda "equal" (lambda "x" (lambda "y"
  (apl (apl (apl (apl (apl (apl (apl (var "x")
   (apl (apl (apl (apl (apl (apl (apl (var "y") LT_K) LT_KI) LT_KI) (apl LT_K LT_KI)) (apl LT_K LT_KI)) (apl LT_K (apl LT_K LT_KI))) (apl LT_K (apl LT_K LT_KI))) )
   (apl (apl (apl (apl (apl (apl (apl (var "y") LT_KI) LT_K) LT_KI) (apl LT_K LT_KI)) (apl LT_K LT_KI)) (apl LT_K (apl LT_K LT_KI))) (apl LT_K (apl LT_K LT_KI))) )
   (apl (apl (apl (apl (apl (apl (apl (var "y") LT_KI) LT_KI) LT_K) (apl LT_K LT_KI)) (apl LT_K LT_KI)) (apl LT_K (apl LT_K LT_KI))) (apl LT_K (apl LT_K LT_KI))) )
   (lambda "a" (apl (apl (apl (apl (apl (apl (apl (var "y") LT_KI) LT_KI) LT_KI) (apl (var "equal") (var "a"))) (apl LT_K LT_KI)) (apl LT_K (apl LT_K LT_KI))) (apl LT_K (apl LT_K LT_KI))) ) )
   (lambda "a" (apl (apl (apl (apl (apl (apl (apl (var "y") LT_KI) LT_KI) LT_KI) (apl LT_K LT_KI)) (apl (var "equal") (var "a"))) (apl LT_K (apl LT_K LT_KI))) (apl LT_K (apl LT_K LT_KI))) ) )
   (lambda "x1" (lambda "x2" (apl (apl (apl (apl (apl (apl (apl (var "y") LT_KI) LT_KI) LT_KI) (apl LT_K LT_KI)) (apl LT_K LT_KI)) 
    (lambda "y1" (lambda "y2" (apl (apl (apl (apl (var "equal") (var "x1")) (var "y1")) (apl (apl (var "equal")(var "x2")) (var "y2"))) LT_KI)))
     ) (apl LT_K (apl LT_K LT_KI))) )) )
   (lambda "x1" (lambda "x2" (apl (apl (apl (apl (apl (apl (apl (var "y") LT_KI) LT_KI) LT_KI) (apl LT_K LT_KI)) (apl LT_K LT_KI)) (apl LT_K (apl LT_K LT_KI)))
    (lambda "y1" (lambda "y2" (apl (apl (apl (apl (var "equal") (var "x1")) (var "y1")) (apl (apl (var "equal")(var "x2")) (var "y2"))) LT_KI)))
     )  )) )
  )))

 LT_shift = apl LT_Y (lambda "shift" (lambda "u" (lambda "x" 
  (apl (apl (apl (apl (var "equal") (var "x")) (var "u")) (apl LT_RDBS (var "u")))
   (apl (apl (apl (apl (apl (apl (apl (var "x")
    LT_RAXM )
    LT_RSMB )
    LT_RDB0 )
    (lambda "x1" (apl LT_RDBS (apl (apl (var "shift") (var "u")) (var "x1")))) )
    (lambda "x1" (apl LT_RDBL (apl (apl (var "shift") (apl LT_RDBS (var "u"))) (var "x1")))) )
    (lambda "x1" (lambda "x2" (apl (apl LT_RAPL 
      (apl (apl (var "shift") (var "u")) (var "x1")) )
      (apl (apl (var "shift") (var "u")) (var "x2")) ) )) )
    (lambda "x1" (lambda "x2" (apl (apl LT_RLTR 
      (apl (apl (var "shift") (var "u")) (var "x1")) )
      (apl (apl (var "shift") (var "u")) (var "x2")) ) )) )
   ))))
    
 LT_subst = apl LT_Y (lambda "subst" (lambda "u" (lambda "a" (lambda "b"
  (apl (apl (apl (apl LT_equal (var "a")) (var "u")) (var "b"))
   (apl (apl (apl (apl (apl (apl (apl (var "a")
    LT_RAXM )
    LT_RSMB )
    LT_RDB0 )
    (lambda "a1" (apl (apl (apl (apl LT_equal (var "a1")) (var "u")) (var "u")) (apl LT_RDBS (apl (apl (apl (var "subst") (var "u")) (var "a1")) (var "b"))))) )
    (lambda "a1" (apl LT_RDBL (apl (apl (apl (var "subst") (apl LT_RDBS (var "u"))) (var "a1")) (apl (apl LT_shift LT_RDB0) (var "b"))))) )
    (lambda "a1" (lambda "a2" (apl (apl LT_RAPL (apl (apl (apl (var "subst") (var "u")) (var "a1")) (var "b"))) (apl (apl (apl (var "subst") (var "u")) (var "a2")) (var "b"))))) )
    (lambda "a1" (lambda "a2" (apl (apl LT_RLTR (apl (apl (apl (var "subst") (var "u")) (var "a1")) (var "b"))) (apl (apl (apl (var "subst") (var "u")) (var "a2")) (var "b"))))))
   )))))

 LT_red1 = apl LT_Y (lambda "red1" (lambda "x" 
  (apl (apl (apl (apl (apl (apl (apl (var "x")
   LT_RAXM )
   LT_RSMB )
   LT_RDB0 )
   (lambda "x1" (apl LT_RDBS (apl (var "red1") (var "x1")))) )
   (lambda "x1" (apl LT_RDBL (apl (var "red1") (var "x1")))) )
   (lambda "x1" (lambda "x2" (apl (apl (apl (apl (apl (apl (apl (var "x1")
    (apl (apl LT_RAPL (apl (var "red1") (var "x1"))) (apl (var "red1") (var "x2"))) )
    (apl (apl LT_RAPL (apl (var "red1") (var "x1"))) (apl (var "red1") (var "x2"))) )
    (apl (apl LT_RAPL (apl (var "red1") (var "x1"))) (apl (var "red1") (var "x2"))) )
    (apl LT_K (apl (apl LT_RAPL (apl (var "red1") (var "x1"))) (apl (var "red1") (var "x2")))) )
    (lambda "x3" (apl (apl (apl LT_subst LT_RDB0) (var "x3")) (var "x2"))) )
    (apl LT_K (apl LT_K (apl (apl LT_RAPL (apl (var "red1") (var "x1"))) (apl (var "red1") (var "x2"))))) )
    (apl LT_K (apl LT_K (apl (apl LT_RAPL (apl (var "red1") (var "x1"))) (apl (var "red1") (var "x2"))))) )
    )) )
   (lambda "x1" (lambda "x2" (apl (apl LT_RLTR (apl (var "red1") (var "x1"))) (apl (var "red1") (var "x2")) ))) )
  ))

 LT_red = apl LT_Y (lambda "red" (lambda "x"
  (apl (lambda "y" (apl (apl (apl (apl LT_equal (var "x")) (var "y")) (var "x")) (apl (var "red") (var "y")))) (apl LT_red1 (var "x"))) ))

 LT_side = apl LT_Y (lambda "side" (lambda "t" (lambda "s" (lambda "x"
  (apl (apl (apl (apl (apl (apl (apl (var "x")
   -- (apl (apl (var "s") (apl (var "t") LT_K)) (apl (var "t") LT_KI)) )
   (apl (apl (var "s") (apl (apl LT_RAPL (var "t")) (repLT LT_K))) (apl (apl LT_RAPL (var "t")) (repLT LT_KI))) )
   -- (apl (var "t") (var "s")) )
   LT_RSMB )
   LT_RDB0 )
   (lambda "x1" (apl LT_RDBS (apl (apl (apl (var "side") (var "t")) (var "s")) (var "x1")))) )
   (lambda "x1" (apl LT_RDBL (apl (apl (apl (var "side") (var "t")) (var "s")) (var "x1")))) )
   (lambda "x1" (lambda "x2" (apl (apl LT_RAPL (apl (apl (apl (var "side") (var "t")) (var "s")) (var "x1"))) (apl (apl (apl (var "side") (var "t")) (var "s")) (var "x2"))))) )
   (lambda "x1" (lambda "x2" 
    (apl (apl (apl (apl (var "equal") (apl (var "red") (apl (apl (apl (var "side") (var "t")) LT_K) (var "x1")))) (apl (var "red") (apl (apl (apl (var "side") (var "t")) LT_K) (var "x2"))))
    (apl LT_red (apl (apl (apl (var "side") (var "t")) LT_KI) (apl (apl (var "s") (var "x1")) (var "x2")))) )
    (apl (apl LT_RLTR (var "x1")) (var "x2")) ) )) ) 
   ))))

 LT_eval = apl LT_Y (lambda "eval" (lambda "x"
  (apl (apl (apl (apl (apl (apl (apl (var "x")
    axm )
    smb )
    db0 )
    (lambda "x1" (dbs (apl (var "eval") (var "x1")))) )
    (lambda "x1" (dbl (apl (var "eval") (var "x1")))) )
    (lambda "x1" (lambda "x2" (apl (apl (var "eval") (var "x1")) (apl (var "eval") (var "x2"))))) )
    (lambda "x1" (lambda "x2" (ltr (apl (var "eval") (var "x1")) (apl (var "eval") (var "x2"))))) )
  ))

 eval : Proof -> Proof
 eval x = red (APL (polt LT_eval) x)

 LT_map = apl LT_Y (lambda "map" (lambda "f" 
  (lambda "g" (apl (apl (apl (apl (apl (apl (apl (var "g")
   (apl (var "f") LT_RAXM) )
   (apl (var "f") LT_RSMB) )
   (apl (var "f") LT_RDB0) )
   (apl (var "map") (lambda "x" (apl (var "f") (apl LT_RDBS (var "x"))))) )
   (apl (var "map") (lambda "x" (apl (var "f") (apl LT_RDBL (var "x"))))) )
   (apl (var "map") (lambda "x" (apl (var "map") (lambda "y" (apl (var "f") (apl (apl LT_RAPL (var "x")) (var "y"))))))) )
   (apl (var "map") (lambda "x" (apl (var "map") (lambda "y" (apl (var "f") (apl (apl LT_RLTR (var "x")) (var "y"))))))) )
  ) ))

 LT_refl = lambda "t" (lambda "s"
  (apl LT_map (lambda "x" (apl LT_eval (apl (apl (apl LT_side (var "t")) (var "s")) (var "x"))))) )

{-
 LT_addrefl = lambda "t"
  (apl (apl LT_P (apl (apl LT_P (apl (var "t") LT_K)) (apl (apl LT_refl (var "t")) LT_K)))
                 (apl (apl LT_P (apl (var "t") LT_KI)) (apl (apl LT_refl (var "t")) LT_KI)))
-}
 
{-
 LT_addrefl = lambda "t"
  (apl (apl LT_P (apl (apl LT_P (apl (apl LT_RAPL (var "t")) (repLT LT_K))) (apl (apl LT_refl (var "t")) LT_K)))
                 (apl (apl LT_P (apl (apl LT_RAPL (var "t")) (repLT LT_KI))) (apl (apl LT_refl (var "t")) LT_KI)))

 addrefl : Proof -> Proof
 addrefl t = APL (APL (polt LT_P) (APL (APL (polt LT_P) (APL t (polt LT_K))) (APL (APL (polt LT_refl) (rep t)) (polt LT_K))))
                                  (APL (APL (polt LT_P) (APL t (polt LT_KI))) (APL (APL (polt LT_refl) (rep t)) (polt LT_KI)))
-}

 LT_addrefl = lambda "t"
  (apl (apl LT_P (apl (apl LT_P (apl (apl LT_refl (var "t")) LT_K)) (apl (apl LT_RAPL (var "t")) (repLT LT_K))))
                 (apl (apl LT_P (apl (apl LT_refl (var "t")) LT_KI)) (apl (apl LT_RAPL (var "t")) (repLT LT_KI))))

 addrefl : Proof -> Proof
 addrefl t = APL (APL (polt LT_P) (APL (APL (polt LT_P) (APL (APL (polt LT_refl) (rep t)) (polt LT_K))) (APL t (polt LT_K))))
                                  (APL (APL (polt LT_P) (APL (APL (polt LT_refl) (rep t)) (polt LT_KI))) (APL t (polt LT_KI)))

 addreflr : Proof -> Proof
 addreflr rt = red (APL (polt LT_addrefl) rt)

{-
 LT_mapnat = apl LT_Y (lambda "mapnat" (lambda "f"
  (lambda "g" (apl (apl (var "g")
   (apl (var "f") LT_zero) )
   (apl (var "mapnat") (lambda "n" (apl (var "f") (apl LT_suc (var "n"))))) ) 
  ) ))
-}

 LT_mapnat = apl LT_Y (lambda "mapnat" (lambda "f"
  (apl (apl LT_P
   (apl (var "f") LT_zero) )
   (apl (var "mapnat") (lambda "n" (apl (var "f") (apl LT_suc (var "n"))))) ) ))

{-
 mapnat : (Nat -> Proof) -> Proof
 mapnat f = APL (APL (polt LT_P) (f O)) (mapnat (\n -> f (1+ n)))
-}

 LT_lim = lambda "f"
  (apl (apl LT_P
   (apl LT_mapnat (lambda "n" (apl (apl (var "f") (var "n")) LT_K))) )
   (apl LT_mapnat (lambda "n" (apl (apl (var "f") (var "n")) LT_KI))) )

 -- lim : (Nat -> Proof) -> Proof
 -- lim f = APL (polt LT_lim) (rep f)

 limr : Proof -> Proof
 limr f = red (APL (polt LT_lim) f)

 -- Ordinals

 data Ord : Set where
  Zero : Ord
  Suc : Ord -> Ord
  Lim : (Nat -> Ord) -> Ord

{- 
 TheoryOfOrd : Ord -> Proof -> Proof
 TheoryOfOrd Zero t = t
 TheoryOfOrd (Suc x) t = addrefl (TheoryOfOrd x t)
 TheoryOfOrd (Lim f) t = lim (\n -> TheoryOfOrd (f n) t)
-}

{- 
 tirp : Ord -> Proof -> Proof
 tirp Zero rt = rt
 tirp (Suc x) rt = addreflr (tirp x rt)
 tirp (Lim f) rt = lim (polt (lambda "n" (apl (apl LT_tirp (apl (repFunc f) (var "n"))) rt)))
-}

 LT_tirp = apl LT_Y (lambda "tirp" (lambda "x" (lambda "t"
  (apl (apl (apl (var "x") 
   (var "t") )
   (lambda "y" (apl LT_addrefl (apl (apl (var "tirp") (var "y")) (var "t")))) )
   (lambda "f" (apl LT_lim (lambda "n" (apl (apl (var "tirp") (apl (var "f") (var "n"))) (var "t"))))) ) )))

{-
 repFunc ???

 repOrd : Ord -> Proof
 repOrd Zero = polt (LT_Zero)
 repOrd (Suc x) = APL (polt LT_Suc) (repOrd x) 
 repOrd (Lim f) = APL (polt LT_Lim) (repFunc f)

 tirpr : Ord -> Proof -> Proof
 tirpr x rt = APL (APL (polt LT_tirp) (repOrd x)) rt
-}

 tirpr : Proof -> Proof -> Proof
 tirpr rx rt = red (APL (APL (polt LT_tirp) rx) rt)

{-
 lim2 : (Nat -> Proof) -> Proof
 lim2 f = polt (lambda "s" (lambda "n" (apl (apl (apl f (apl LT_f1 (var "n"))) (var "s")) (apl LT_f2 (var "n")))))
-}

{-
 tirp : Ord -> (Bool -> Nat -> Proof) -> Bool -> Nat -> Proof
 tirp Zero t s n = t s n
 tirp (Suc x) t s n = pair (tirp x t s n) (reflx s (tirp x t true n) (tirp x t false n))
 tirp (Lim f) t s n = tirp (f (f2 n)) t s (f1 n) 
-}




