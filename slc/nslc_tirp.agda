module nslc_tirp where

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
  SMB : String -> Proof
  DB0 : Proof
  DBS : Proof -> Proof
  DBL : Proof -> Proof
  APL : Proof -> Proof -> Proof
  LTR : Proof -> Proof -> Proof

-- Syntactic equality of proofs
 _===_ : Proof -> Proof -> Bool
 AXM === AXM = true
 SMB s1 === SMB s2 = s1 eq s2
 DB0 === DB0 = true
 DBS x === DBS y = x === y
 DBL x === DBL y = x === y
 APL x y === APL x' y' = (x === x') and (y === y')
 LTR x y === LTR x' y' = (x === x') and (y === y')
 x === y = false

 shift : Proof -> Proof -> Proof
 shift u AXM = AXM
 shift u (SMB s) = (SMB s)
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
 -- side : (Bool -> Proof) -> Bool -> Proof -> Proof
 side t s AXM = if s then (APL t (DBL (DBL (DBS DB0)))) else (APL t (DBL (DBL DB0)))
 -- side t s AXM = t s
 side _ _ (SMB s) = SMB s
 side _ _ DB0 = DB0
 side _ _ (DBS x) = DBS x
 side t s (DBL x) = DBL (side t s x)
 side t s (APL x y) = APL (side t s x) (side t s y)
 side t s (LTR x y) = if red (side t true x) === red (side t true y) then (if s then red (side t false x) else red (side t false y)) else (LTR x y)

 var : String -> Proof
 var x = SMB x

 _contSmb_ : Proof -> String -> Bool
 AXM contSmb _ = false
 (SMB s1) contSmb s2 = s1 eq s2
 DB0 contSmb _ = false
 (DBS x) contSmb s = x contSmb s
 (DBL x) contSmb s = x contSmb s
 (APL x y) contSmb s = (x contSmb s) or (y contSmb s)
 (LTR x y) contSmb s = (x contSmb s) or (y contSmb s)

 abstr : Proof -> String -> Proof -> Proof
 abstr1 : Proof -> String -> Proof -> Proof
 abstr d v x = if (x contSmb v) then (abstr1 d v x) else x
 abstr1 _ _ AXM = AXM
 abstr1 d v (SMB s) = if v eq s then d else (SMB s)
 abstr1 _ _ DB0 = DB0
 abstr1 d v (DBS x) = DBS (abstr d v x)
 abstr1 d v (DBL x) = DBL (abstr (DBS d) v x)
 abstr1 d v (APL x y) = APL (abstr d v x) (abstr d v y)
 abstr1 d v (LTR x y) = LTR (abstr d v x) (abstr d v y)
 
 lambda : String -> Proof -> Proof
 lambda v x = DBL (abstr DB0 v x)

 APL2 : Proof -> Proof -> Proof -> Proof
 APL2 f a b = APL (APL f a) b

 APL3 : Proof -> Proof -> Proof -> Proof -> Proof
 APL3 f a b c = APL (APL (APL f a) b) c

 I = lambda "a" (var "a")
 K = lambda "a" (lambda "b" (var "a"))
 S = lambda "a" (lambda "b" (lambda "c" (APL2 (var "a") (var "c") (APL (var "b") (var "c")))))
 KI = lambda "a" (lambda "b" (var "b"))
 P = lambda "a" (lambda "b" (lambda "f" (APL2 (var "f") (var "a") (var "b"))))
 B = lambda "f" (lambda "g" (lambda "x" (APL (var "f") (APL (var "g") (var "x")))))
 A = lambda "x" (APL (var "x") (var "x"))
 Y = lambda "f" (APL A (APL2 B (var "f") A))
 rzero = K
 rsuc = lambda "n" (lambda "z" (lambda "s" (APL (var "s") (var "n"))))
 rZero = lambda "z" (lambda "s" (lambda "l" (var "z")))
 rSuc = lambda "a" (lambda "z" (lambda "s" (lambda "l" (APL (var "s") (var "a")))))
 rLim = lambda "f" (lambda "z" (lambda "s" (lambda "l" (APL (var "l") (var "f")))))

 RAXM = lambda "axm" (lambda "smb" (lambda "db0" (lambda "dbs" (lambda "dbl" (lambda "APL" (lambda "ltr" (var "axm")))))))
 RSMB = lambda "axm" (lambda "smb" (lambda "db0" (lambda "dbs" (lambda "dbl" (lambda "APL" (lambda "ltr" (var "smb")))))))
 RDB0 = lambda "axm" (lambda "smb" (lambda "db0" (lambda "dbs" (lambda "dbl" (lambda "APL" (lambda "ltr" (var "db0")))))))
 RDBS = lambda "x" (lambda "axm" (lambda "smb" (lambda "db0" (lambda "dbs" (lambda "dbl" (lambda "APL" (lambda "ltr" (APL (var "dbs") (var "x")))))))))
 RDBL = lambda "x" (lambda "axm" (lambda "smb" (lambda "db0" (lambda "dbs" (lambda "dbl" (lambda "APL" (lambda "ltr" (APL (var "dbl") (var "x")))))))))
 RAPL = lambda "x" (lambda "y" (lambda "axm" (lambda "smb" (lambda "db0" (lambda "dbs" (lambda "dbl" (lambda "APL" (lambda "ltr" (APL2 (var "APL") (var "x") (var "y"))))))))))
 RLTR = lambda "x" (lambda "y" (lambda "axm" (lambda "smb" (lambda "db0" (lambda "dbs" (lambda "dbl" (lambda "APL" (lambda "ltr" (APL2 (var "ltr") (var "x") (var "y"))))))))))

 rep : Proof -> Proof
 rep AXM = RAXM
 rep (SMB s) = RSMB
 rep DB0 = RDB0
 rep (DBS x) = APL RDBS (rep x)
 rep (DBL x) = APL RDBL (rep x)
 rep (APL x y) = APL2 RAPL (rep x) (rep y)
 rep (LTR x y) = APL2 RAPL (rep x) (rep y)
 
 requal = APL Y (lambda "equal" (lambda "x" (lambda "y"
  (APL (APL (APL (APL (APL (APL (APL (var "x")
   (APL (APL (APL (APL (APL (APL (APL (var "y") K) KI) KI) (APL K KI)) (APL K KI)) (APL K (APL K KI))) (APL K (APL K KI))) )
   (APL (APL (APL (APL (APL (APL (APL (var "y") KI) K) KI) (APL K KI)) (APL K KI)) (APL K (APL K KI))) (APL K (APL K KI))) )
   (APL (APL (APL (APL (APL (APL (APL (var "y") KI) KI) K) (APL K KI)) (APL K KI)) (APL K (APL K KI))) (APL K (APL K KI))) )
   (lambda "a" (APL (APL (APL (APL (APL (APL (APL (var "y") KI) KI) KI) (APL (var "equal") (var "a"))) (APL K KI)) (APL K (APL K KI))) (APL K (APL K KI))) ) )
   (lambda "a" (APL (APL (APL (APL (APL (APL (APL (var "y") KI) KI) KI) (APL K KI)) (APL (var "equal") (var "a"))) (APL K (APL K KI))) (APL K (APL K KI))) ) )
   (lambda "x1" (lambda "x2" (APL (APL (APL (APL (APL (APL (APL (var "y") KI) KI) KI) (APL K KI)) (APL K KI)) 
    (lambda "y1" (lambda "y2" (APL (APL (APL (APL (var "equal") (var "x1")) (var "y1")) (APL (APL (var "equal")(var "x2")) (var "y2"))) KI)))
     ) (APL K (APL K KI))) )) )
   (lambda "x1" (lambda "x2" (APL (APL (APL (APL (APL (APL (APL (var "y") KI) KI) KI) (APL K KI)) (APL K KI)) (APL K (APL K KI)))
    (lambda "y1" (lambda "y2" (APL (APL (APL (APL (var "equal") (var "x1")) (var "y1")) (APL (APL (var "equal")(var "x2")) (var "y2"))) KI)))
     )  )) )
  )))

 rshift = APL Y (lambda "shift" (lambda "u" (lambda "x" 
  (APL (APL (APL (APL (var "equal") (var "x")) (var "u")) (APL RDBS (var "u")))
   (APL (APL (APL (APL (APL (APL (APL (var "x")
    RAXM )
    RSMB )
    RDB0 )
    (lambda "x1" (APL RDBS (APL (APL (var "shift") (var "u")) (var "x1")))) )
    (lambda "x1" (APL RDBL (APL (APL (var "shift") (APL RDBS (var "u"))) (var "x1")))) )
    (lambda "x1" (lambda "x2" (APL (APL RAPL 
      (APL (APL (var "shift") (var "u")) (var "x1")) )
      (APL (APL (var "shift") (var "u")) (var "x2")) ) )) )
    (lambda "x1" (lambda "x2" (APL (APL RLTR 
      (APL (APL (var "shift") (var "u")) (var "x1")) )
      (APL (APL (var "shift") (var "u")) (var "x2")) ) )) )
   ))))
    
 rsubst = APL Y (lambda "subst" (lambda "u" (lambda "a" (lambda "b"
  (APL (APL (APL (APL requal (var "a")) (var "u")) (var "b"))
   (APL (APL (APL (APL (APL (APL (APL (var "a")
    RAXM )
    RSMB )
    RDB0 )
    (lambda "a1" (APL (APL (APL (APL requal (var "a1")) (var "u")) (var "u")) (APL RDBS (APL (APL (APL (var "subst") (var "u")) (var "a1")) (var "b"))))) )
    (lambda "a1" (APL RDBL (APL (APL (APL (var "subst") (APL RDBS (var "u"))) (var "a1")) (APL (APL rshift RDB0) (var "b"))))) )
    (lambda "a1" (lambda "a2" (APL (APL RAPL (APL (APL (APL (var "subst") (var "u")) (var "a1")) (var "b"))) (APL (APL (APL (var "subst") (var "u")) (var "a2")) (var "b"))))) )
    (lambda "a1" (lambda "a2" (APL (APL RLTR (APL (APL (APL (var "subst") (var "u")) (var "a1")) (var "b"))) (APL (APL (APL (var "subst") (var "u")) (var "a2")) (var "b"))))))
   )))))

 rred1 = APL Y (lambda "red1" (lambda "x" 
  (APL (APL (APL (APL (APL (APL (APL (var "x")
   RAXM )
   RSMB )
   RDB0 )
   (lambda "x1" (APL RDBS (APL (var "red1") (var "x1")))) )
   (lambda "x1" (APL RDBL (APL (var "red1") (var "x1")))) )
   (lambda "x1" (lambda "x2" (APL (APL (APL (APL (APL (APL (APL (var "x1")
    (APL (APL RAPL (APL (var "red1") (var "x1"))) (APL (var "red1") (var "x2"))) )
    (APL (APL RAPL (APL (var "red1") (var "x1"))) (APL (var "red1") (var "x2"))) )
    (APL (APL RAPL (APL (var "red1") (var "x1"))) (APL (var "red1") (var "x2"))) )
    (APL K (APL (APL RAPL (APL (var "red1") (var "x1"))) (APL (var "red1") (var "x2")))) )
    (lambda "x3" (APL (APL (APL rsubst RDB0) (var "x3")) (var "x2"))) )
    (APL K (APL K (APL (APL RAPL (APL (var "red1") (var "x1"))) (APL (var "red1") (var "x2"))))) )
    (APL K (APL K (APL (APL RAPL (APL (var "red1") (var "x1"))) (APL (var "red1") (var "x2"))))) )
    )) )
   (lambda "x1" (lambda "x2" (APL (APL RLTR (APL (var "red1") (var "x1"))) (APL (var "red1") (var "x2")) ))) )
  ))

 rred = APL Y (lambda "red" (lambda "x"
  (APL (lambda "y" (APL (APL (APL (APL requal (var "x")) (var "y")) (var "x")) (APL (var "red") (var "y")))) (APL rred1 (var "x"))) ))

 rside = APL Y (lambda "side" (lambda "t" (lambda "s" (lambda "x"
  (APL (APL (APL (APL (APL (APL (APL (var "x")
   -- (APL (APL (var "s") (APL (var "t") K)) (APL (var "t") KI)) )
   (APL (APL (var "s") (APL (APL RAPL (var "t")) (rep K))) (APL (APL RAPL (var "t")) (rep KI))) )
   -- (APL (var "t") (var "s")) )
   RSMB )
   RDB0 )
   (lambda "x1" (APL RDBS (APL (APL (APL (var "side") (var "t")) (var "s")) (var "x1")))) )
   (lambda "x1" (APL RDBL (APL (APL (APL (var "side") (var "t")) (var "s")) (var "x1")))) )
   (lambda "x1" (lambda "x2" (APL (APL RAPL (APL (APL (APL (var "side") (var "t")) (var "s")) (var "x1"))) (APL (APL (APL (var "side") (var "t")) (var "s")) (var "x2"))))) )
   (lambda "x1" (lambda "x2" 
    (APL (APL (APL (APL (var "equal") (APL (var "red") (APL (APL (APL (var "side") (var "t")) K) (var "x1")))) (APL (var "red") (APL (APL (APL (var "side") (var "t")) K) (var "x2"))))
    (APL rred (APL (APL (APL (var "side") (var "t")) KI) (APL (APL (var "s") (var "x1")) (var "x2")))) )
    (APL (APL RLTR (var "x1")) (var "x2")) ) )) ) 
   ))))

 reval = APL Y (lambda "eval" (lambda "x"
  (APL (APL (APL (APL (APL (APL (APL (var "x")
    AXM )
    (SMB "SMB"))
    DB0 )
    (lambda "x1" (DBS (APL (var "eval") (var "x1")))) )
    (lambda "x1" (DBL (APL (var "eval") (var "x1")))) )
    (lambda "x1" (lambda "x2" (APL (APL (var "eval") (var "x1")) (APL (var "eval") (var "x2"))))) )
    (lambda "x1" (lambda "x2" (LTR (APL (var "eval") (var "x1")) (APL (var "eval") (var "x2"))))) )
  ))

 rmap = APL Y (lambda "map" (lambda "f" 
  (lambda "g" (APL (APL (APL (APL (APL (APL (APL (var "g")
   (APL (var "f") RAXM) )
   (APL (var "f") RSMB) )
   (APL (var "f") RDB0) )
   (APL (var "map") (lambda "x" (APL (var "f") (APL RDBS (var "x"))))) )
   (APL (var "map") (lambda "x" (APL (var "f") (APL RDBL (var "x"))))) )
   (APL (var "map") (lambda "x" (APL (var "map") (lambda "y" (APL (var "f") (APL (APL RAPL (var "x")) (var "y"))))))) )
   (APL (var "map") (lambda "x" (APL (var "map") (lambda "y" (APL (var "f") (APL (APL RLTR (var "x")) (var "y"))))))) )
  ) ))

 rrefl = lambda "t" (lambda "s"
  (APL rmap (lambda "x" (APL reval (APL (APL (APL rside (var "t")) (var "s")) (var "x"))))) )

 raddrefl = lambda "t"
  (APL2 P 
   (APL2 P (APL2 rrefl (var "t") K) (APL2 RAPL (var "t") (rep K)))
   (APL2 P (APL2 rrefl (var "t") KI) (APL2 RAPL (var "t") (rep KI))) )

 rmapnat = APL Y (lambda "mapnat" (lambda "f"
  (APL (APL P
   (APL (var "f") rzero) )
   (APL (var "mapnat") (lambda "n" (APL (var "f") (APL rsuc (var "n"))))) ) ))

 rlim = lambda "f"
  (APL (APL P
   (APL rmapnat (lambda "n" (APL (APL (var "f") (var "n")) K))) )
   (APL rmapnat (lambda "n" (APL (APL (var "f") (var "n")) KI))) )

 rtirp = APL Y (lambda "tirp" (lambda "x" (lambda "t"
  (APL (APL (APL (var "x") 
   (var "t") )
   (lambda "y" (APL raddrefl (APL (APL (var "tirp") (var "y")) (var "t")))) )
   (lambda "f" (APL rlim (lambda "n" (APL (APL (var "tirp") (APL (var "f") (var "n"))) (var "t"))))) ) )))

 rpt = APL Y (lambda "rpt" (lambda "n" (lambda "f" (lambda "x"
  (APL2 (var "n")
   (var "x")
   (lambda "p" (APL (var "f") (APL3 (var "rpt") (var "p") (var "f") (var "x")))) ) ))))

 fix = lambda "f" (lambda "x" (APL rlim (lambda "n" (APL3 rpt (var "n") (var "f") (var "x")))))

 w = APL2 fix rSuc rZero
