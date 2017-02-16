module Refl where

 import Slcn

 mtrue = lambda "t" $ lambda "f" $ var "t"
 mfalse = lambda "t" $ lambda "f" $ var "f"

 mpair = lambda "x" $ lambda "y" $ lambda "f" $ apl2 (var "f") (var "x") (var "y")
 mfst = lambda "p" $ apl (var "p") (lambda "x" $ lambda "y" (var "x"))
 msnd = lambda "p" $ apl (var "p") (lambda "x" $ lambda "y" (var "y"))

 combk = lambda "x" $ lambda "y" $ var "x"

 mleftside = lambda "l" $ lambda "r" $ var "l"
 mrightside = lambda "l" $ lambda "r" $ var "r"

 smb1 = smb "SMB"
 sdb0 = smb "sdb0"

 maxm = 
  lambda "axm" $ lambda "smb" $ lambda "db0" $ lambda "dbs" $ lambda "dbl" $ lambda "apl" $ lambda "ltr" $ 
  var "axm"

 msmb = 
  lambda "axm" $ lambda "smb" $ lambda "db0" $ lambda "dbs" $ lambda "dbl" $ lambda "apl" $ lambda "ltr" $ 
  var "smb"

 mdb0 = 
  lambda "axm" $ lambda "smb" $ lambda "db0" $ lambda "dbs" $ lambda "dbl" $ lambda "apl" $ lambda "ltr" $ 
  var "db0"

 mdbs = lambda "x" $ 
  lambda "axm" $ lambda "smb" $ lambda "db0" $ lambda "dbs" $ lambda "dbl" $ lambda "apl" $ lambda "ltr" $ 
  apl (var "dbs") (var "x")

 mdbl = lambda "x" $
  lambda "axm" $ lambda "smb" $ lambda "db0" $ lambda "dbs" $ lambda "dbl" $ lambda "apl" $ lambda "ltr" $ 
  apl (var "dbl") (var "x")

 mapl = lambda "x" $ lambda "y" $ 
  lambda "axm" $ lambda "smb" $ lambda "db0" $ lambda "dbs" $ lambda "dbl" $ lambda "apl" $ lambda "ltr" $ 
  apl2 (var "apl") (var "x") (var "y") 

 mltr = lambda "x" $ lambda "y" $ 
  lambda "axm" $ lambda "smb" $ lambda "db0" $ lambda "dbs" $ lambda "dbl" $ lambda "apl" $ lambda "ltr" $ 
  apl2 (var "ltr") (var "x") (var "y")

 rep :: Proof -> Proof
 rep (Proof0 AXM) = maxm
 rep (Proof0 (SMB s)) = msmb
 rep (Proof0 DB0) = mdb0
 rep (Proof1 DBS x) = apl mdbs (rep x)
 rep (Proof1 DBL x) = apl mdbl (rep x)
 rep (Proof2 APL x y) = apl2 mapl (rep x) (rep y)
 rep (Proof2 LTR x y) = apl2 mltr (rep x) (rep y)
 rep _ = msmb

 mrep = fix $ lambda "rep" $ lambda "x"$ apl7 (var "x")
  (rep maxm)
  (rep msmb)
  (rep mdb0)
  (lambda "x1" $ apl2 mapl (rep mdbs) (apl (var "rep") (var "x1")))
  (lambda "x1" $ apl2 mapl (rep mdbl) (apl (var "rep") (var "x1")))
  (lambda "x1" $ lambda "y1" $ apl2 mapl (apl2 mapl (rep mapl) (apl (var "rep") (var "x1"))) (apl (var "rep") (var "y1")))
  (lambda "x1" $ lambda "y1" $ apl2 mapl (apl2 mapl (rep mltr) (apl (var "rep") (var "x1"))) (apl (var "rep") (var "y1")))


 mequal = fix $ lambda "equal" $ lambda "x" $ lambda "y" $ 
  apl7 (var "x") 
   (apl7 (var "y") mtrue  mfalse mfalse (apl combk mfalse) (apl combk mfalse) (apl combk $ apl combk mfalse) (apl combk $ apl combk mfalse))
   (apl7 (var "y") mfalse mtrue  mfalse (apl combk mfalse) (apl combk mfalse) (apl combk $ apl combk mfalse) (apl combk $ apl combk mfalse))
   (apl7 (var "y") mfalse mfalse mtrue  (apl combk mfalse) (apl combk mfalse) (apl combk $ apl combk mfalse) (apl combk $ apl combk mfalse))
   (lambda "a" $ 
    apl7 (var "y") mfalse mfalse mfalse (apl (var "equal") (var "a")) 
                                                           (apl combk mfalse) (apl combk $ apl combk mfalse) (apl combk $ apl combk mfalse))
   (lambda "a" $
    apl7 (var "y") mfalse mfalse mfalse (apl combk mfalse) (apl (var "equal") (var "a"))
                                                                              (apl combk $ apl combk mfalse) (apl combk $ apl combk mfalse))
   (lambda "x1" $ lambda "x2" $
    apl7 (var "y") mfalse mfalse mfalse (apl combk mfalse) (apl combk mfalse) 
    (lambda "y1" $ lambda "y2" $ apl2 (apl2 (var "equal") (var "x1") (var "y1")) (apl2 (var "equal") (var "x2") (var "y2")) mfalse)
                                                                                                             (apl combk $ apl combk mfalse))
   (lambda "x1" $ lambda "x2" $ 
    apl7 (var "y") mfalse mfalse mfalse (apl combk mfalse) (apl combk mfalse) (apl combk $ apl combk mfalse) 
    (lambda "y1" $ lambda "y2" $ apl2 (apl2 (var "equal") (var "x1") (var "y1")) (apl2 (var "equal") (var "x2") (var "y2")) mfalse)
   )

 mshift = fix $ lambda "shift" $ lambda "u" $ lambda "x" $ 
  apl2 (apl2 mequal (var "x") (var "u")) (apl mdbs (var "u")) $
  apl7 (var "x")
   maxm
   msmb
   mdb0
   (lambda "x1" $ apl mdbs $ apl2 (var "shift") (var "u") (var "x1"))
   (lambda "x1" $ apl mdbl $ apl2 (var "shift") (apl mdbs (var "u")) (var "x1"))
   (lambda "x1" $ lambda "x2" $ apl2 mapl (apl2 (var "shift") (var "u") (var "x1")) (apl2 (var "shift") (var "u") (var "x2")))
   (lambda "x1" $ lambda "x2" $ apl2 mltr (apl2 (var "shift") (var "u") (var "x1")) (apl2 (var "shift") (var "u") (var "x2")))

 msubst = fix $ lambda "subst" $ lambda "u" $ lambda "a" $ lambda "b" $
  apl2 (apl2 mequal (var "a") (var "u")) (var "b") $
  apl7 (var "a")
   maxm
   msmb
   mdb0
   (lambda "a1" $ apl2 (apl2 mequal (var "a1") (var "u")) (var "u") $ apl mdbs $ apl3 (var "subst") (var "u") (var "a1") (var "b"))
-- (lambda "a1" $ apl mdbl $ apl3 (var "subst") (apl mdbs (var "u")) (var "a1") (apl2 mshift mdb0 (var "b")))
   (lambda "a1" $ apl mdbl $ apl3 (var "subst") (apl mdbs (var "u")) (var "a1") (apl2 mshift (var "u") (var "b")))
   (lambda "a1" $ lambda "a2" $ apl2 mapl (apl3 (var "subst") (var "u") (var "a1") (var "b")) 
                                          (apl3 (var "subst") (var "u") (var "a2") (var "b")) )
   (lambda "a1" $ lambda "a2" $ apl2 mltr (apl3 (var "subst") (var "u") (var "a1") (var "b")) 
                                          (apl3 (var "subst") (var "u") (var "a2") (var "b")) )


 mred1a = fix $ lambda "red1" $ lambda "x" $
  apl7 (var "x") 
   maxm
   msmb
   mdb0
   (lambda "x1" $ apl mdbs $ apl (var "red1") (var "x1"))
   (lambda "x1" $ apl mdbl $ apl (var "red1") (var "x1"))
   (lambda "x1" $ lambda "x2" $ apl7 (var "x1") 
    (apl2 mapl (apl (var "red1") (var "x1")) (apl (var "red1") (var "x2")))
    (apl2 mapl (apl (var "red1") (var "x1")) (apl (var "red1") (var "x2")))
    (apl2 mapl (apl (var "red1") (var "x1")) (apl (var "red1") (var "x2")))
    (apl combk $ apl2 mapl (apl (var "red1") (var "x1")) (apl (var "red1") (var "x2")))
    (lambda "x3" $ apl3 msubst mdb0 (var "x3") (var "x2"))
    (apl combk $ apl combk $ apl2 mapl (apl (var "red1") (var "x1")) (apl (var "red1") (var "x2")))
    (apl combk $ apl combk $ apl2 mapl (apl (var "red1") (var "x1")) (apl (var "red1") (var "x2"))))
   (lambda "x1" $ lambda "x2" $ apl2 mltr (apl (var "red1") (var "x1")) (apl (var "red1") (var "x2")))


 mred1 = fix $ lambda "red1" $ lambda "x" $
  apl7 (var "x") 
   -- x = AXM
   maxm
   -- x = SMB
   msmb
   -- x = DB0
   mdb0
   -- x = DBS x1
   (lambda "x1" $ apl mdbs $ apl (var "red1") (var "x1"))
   -- x = DBL x1
   (lambda "x1" $ apl mdbl $ apl (var "red1") (var "x1"))
   -- x = APL x1 y1
   (lambda "x1" $ lambda "y1" $ apl7 (var "x1") 
    -- x1 = AXM
    (apl2 mapl (apl (var "red1") (var "x1")) (apl (var "red1") (var "y1")))
    -- x1 = SMB
    (apl2 mapl (apl (var "red1") (var "x1")) (apl (var "red1") (var "y1")))
    -- x1 = DB0
    (apl2 mapl (apl (var "red1") (var "x1")) (apl (var "red1") (var "y1")))
    -- x1 = DBS _
    -- (apl combk $ apl2 mapl (apl (var "red1") (var "x1")) (apl (var "red1") (var "y1")))
    (apl combk $
     apl (lambda "x2" $ 
          apl4 mequal (var "x1") (var "x2") 
           (apl2 mapl (var "x2") (apl (var "red1") (var "y1"))) 
           (apl2 mapl (var "x2") (var "y1")))
      (apl (var "red1") (var "x1")) )
    -- x1 = DBL x2
    (lambda "x2" $ apl3 msubst mdb0 (var "x2") (var "y1"))
    -- x1 = APL _ _
    -- (apl combk $ apl combk $ apl2 mapl (apl (var "red1") (var "x1")) (apl (var "red1") (var "y1")))
    (apl combk $ apl combk $
     apl (lambda "x2" $ 
          apl4 mequal (var "x1") (var "x2") 
           (apl2 mapl (var "x2") (apl (var "red1") (var "y1"))) 
           (apl2 mapl (var "x2") (var "y1")))
      (apl (var "red1") (var "x1")) )
    -- x1 = LTR _ _
    -- (apl combk $ apl combk $ apl2 mapl (apl (var "red1") (var "x1")) (apl (var "red1") (var "y1"))))
    (apl combk $ apl combk $
     apl (lambda "x2" $ 
          apl4 mequal (var "x1") (var "x2") 
           (apl2 mapl (var "x2") (apl (var "red1") (var "y1"))) 
           (apl2 mapl (var "x2") (var "y1")))
      (apl (var "red1") (var "x1")) ) )
   -- x = LTR x y
   -- (lambda "x1" $ lambda "x2" $ apl2 mltr (apl (var "red1") (var "x1")) (apl (var "red1") (var "x2")))
   (lambda "x1" $ lambda "y1" $ 
    apl (lambda "x2" $ 
         apl4 mequal (var "x1") (var "x2") 
          (apl2 mltr (var "x2") (apl (var "red1") (var "y1"))) 
          (apl2 mltr (var "x2") (var "y1")) )
     (apl (var "red1") (var "x1")) )

 mred = fix $ lambda "red" $ lambda "x" $
  apl (lambda "y" $ apl2 (apl2 mequal (var "x") (var "y")) (var "x") (apl (var "red") (var "y"))) (apl mred1 (var "x"))

 mside = fix $ lambda "side" $ lambda "s" $ lambda "u" $ lambda "v" $ lambda "x" $ apl7 (var "x") 
  (apl2 (var "s") (var "u") (var "v"))
  msmb
  mdb0
  (lambda "x1" $ apl mdbs $ apl4 (var "side") (var "s") (var "u") (var "v") (var "x1"))
  (lambda "x1" $ apl mdbl $ apl4 (var "side") (var "s") (var "u") (var "v") (var "x1"))
  (lambda "x1" $ lambda "x2" $ apl2 mapl (apl4 (var "side") (var "s") (var "u") (var "v") (var "x1"))
                                         (apl4 (var "side") (var "s") (var "u") (var "v") (var "x2")))
  (lambda "x1" $ lambda "x2" $ 
   apl2 (apl2 mequal (apl mred $ apl4 (var "side") mleftside (var "u") (var "v") (var "x1"))
                     (apl mred $ apl4 (var "side") mleftside (var "u") (var "v") (var "x2")))
    (apl mred $ apl4 (var "side") mrightside (var "u") (var "v") (apl2 (var "s") (var "x1") (var "x2")))
    (apl2 mltr (var "x1") (var "x2")))

 switchside LeftSide u v = u
 switchside RightSide u v = v

 -- mcontSmb = fix $ lambda "mcontSmb" $ lambda "x" $ lambda "y" $ apl7 (var x)

 -- mapproof f = f axm
 -- mapproof f = f smb1
 mapproof f = apl2 mpair (f axm) (f smb1)
 -- mapproof f = lambda "g" $ apl2 (var "g") (f axm) (f smb1) 
 -- mapproof f = lambda "g" $ apl f (apl2 (var "g") maxm msmb)

 {-
 mapproof f = lambda "x" $ apl7 (var "x")
  -- f (eval (var "x")) ? 
  (f axm)
  (f smb1)
  (f db0)
  (mapproof $ \x1 -> f (dbs x1))
  (mapproof $ \x1 -> f (dbl x1))
  (mapproof $ \x1 -> mapproof $ \x2 -> f (apl x1 x2))
  (mapproof $ \x1 -> mapproof $ \x2 -> f (ltr x1 x2))

 mapproof f = fix $ lambda "r" $ apl7 (var "x") 
  (f axm)
  (f smb1)
  (f db0)
  ...?...

 mapproof f = lambda "x" $ apl7 (var "x")
  (f axm)
  (f smb1)
  (f db0)
  ?
 -}

 mmapproof = fix $ lambda "mapproof" $ lambda "f" $
  lambda "x" $ apl7 (var "x") 
   (apl (var "f") maxm)
   (apl (var "f") msmb)
   (apl (var "f") mdb0)
   (apl (var "mapproof") $ lambda "x1" $ apl (var "f") $ apl mdbs (var "x1"))
   (apl (var "mapproof") $ lambda "x1" $ apl (var "f") $ apl mdbl (var "x1"))
   (apl (var "mapproof") $ lambda "x1" $ apl (var "mapproof") $ lambda "x2" $
    apl (var "f") $ apl2 mapl (var "x1") (var "x2"))
   (apl (var "mapproof") $ lambda "x1" $ apl (var "mapproof") $ lambda "x2" $
    apl (var "f") $ apl2 mltr (var "x1") (var "x2"))

 mzero = lambda "z" $ lambda "s" (var "z")
 msucc = lambda "n" $ lambda "z" $ lambda "s" $ apl (var "s") (var "n")

 mmapnat = fix $ lambda "mapnat" $ lambda "f" $
  lambda "n" $ apl2 (var "n")
   (apl (var "f") mzero)
   (apl (var "mmapnat") $ lambda "n1" $ apl (var "f") $ apl msucc (var "n1"))
   

 refl s u v = apl2 mpair (switchside s u v) (mapproof (side s u v))
 -- refl s u v = apl2 mpair (switchside s u v) (mapproof $ lambda "x" $ apl4 mside (switchside s mleftside mrightside) (rep u) (rep v) (var "x"))

{-
 meval1 = lambda "eval" $ lambda "x" $ apl7 (var "x")
  axm
  smb1
  -- (dbs $ dbs $ dbs $ dbs $ dbs $ dbs db0)
  -- (dbs $ dbs $ dbs db0)
  sdb0
  (lambda "x1" $ dbs $ apl (var "eval") (var "x1"))
  -- (lambda "x1" $ dbl $ apl (var "eval") (var "x1"))
  (lambda "x1" $ apl7 (var "x1")
   (dbl axm)
   (dbl smb1)
   (dbl db0)
   (lambda "x2" $ dbl $ dbs $ apl (var "eval") (var "x2"))
   (lambda "x2" $ dbl $ dbl $ apl (var "eval") (var "x2"))
   -- (lambda "x2" $ dbl $ apl (var "eval") $ apl mdbl (var "x2"))
   {-
   (lambda "x2" $ apl7 (var "x2")
    (dbl (dbl axm))
    (dbl (dbl smb1))
    (dbl (dbl db0))
    (lambda "x3" $ dbl $ dbl $ dbs $ apl (var "eval") (var "x3"))
    {-
    (lambda "x3" $ apl7 (var "x3")
     (dbl $ dbl $ dbs axm)
     (dbl $ dbl $ dbs smb1)
     (dbl $ dbl $ dbs db0)
     (lambda "x4" $ dbl $ dbl $ dbs $ dbs $ apl (var "eval") (var "x4"))
     (lambda "x4" $ dbl $ dbl $ dbs $ dbl $ apl (var "eval") (var "x4"))
     (lambda "x4" $ lambda "y4" $ dbl $ dbl $ dbs $ apl (apl (var "eval") (var "x4")) (apl (var "eval") (var "y4")))
     (lambda "x4" $ lambda "y4" $ dbl $ dbl $ dbs $ ltr (apl (var "eval") (var "x4")) (apl (var "eval") (var "y4"))) )
    -}
    (lambda "x3" $ dbl $ dbl $ dbl $ apl (var "eval") (var "x3"))
    (lambda "x3" $ lambda "y3" $ dbl $ dbl $ apl (apl (var "eval") (var "x3")) (apl (var "eval") (var "y3")))
    (lambda "x3" $ lambda "y3" $ dbl $ dbl $ ltr (apl (var "eval") (var "x3")) (apl (var "eval") (var "y3"))) )
   -}
   (lambda "x2" $ lambda "y2" $ dbl $ apl (apl (var "eval") (var "x2")) (apl (var "eval") (var "y2")))
   (lambda "x2" $ lambda "y2" $ dbl $ ltr (apl (var "eval") (var "x2")) (apl (var "eval") (var "y2"))) )
  (lambda "x1" $ lambda "x2" $ apl (apl (var "eval") (var "x1")) (apl (var "eval") (var "x2")))
  (lambda "x1" $ lambda "x2" $ ltr (apl (var "eval") (var "x1")) (apl (var "eval") (var "x2")))
-}

{-
 meval1 = lambda "eval" $ lambda "x" $ apl7 (var "x")
  axm
  smb1
  sdb0
  (lambda "x1" $ dbs $ apl (var "eval") (var "x1"))
  -- (lambda "x1" $ lambda "sdb0" $ reduce $ apl (var "eval") (var "x1"))
  (lambda "x1" $ dbl $ subst sdb0 (apl (var "eval") (var "x1")) db0)
  (lambda "x1" $ lambda "x2" $ apl (apl (var "eval") (var "x1")) (apl (var "eval") (var "x2")))
  (lambda "x1" $ lambda "x2" $ ltr (apl (var "eval") (var "x1")) (apl (var "eval") (var "x2")))
-}

 munshift = fix $ lambda "unshift" $ lambda "x" $ apl7 (var "x")
  maxm
  msmb
  mdb0
  (lambda "x1" (var "x1"))
  (lambda "x1" $ apl mdbl (apl (var "unshift") (var "x1")))
  (lambda "x1" $ lambda "y1" $ apl2 mapl (apl (var "unshift") (var "x1")) (apl (var "unshift") (var "y1")))
  (lambda "x1" $ lambda "y1" $ apl2 mltr (apl (var "unshift") (var "x1")) (apl (var "unshift") (var "y1"))) 


 meval1 = lambda "eval" $ lambda "x" $ apl7 (var "x")
  axm
  smb1
  (dbs $ dbs $ dbs db0)
  (lambda "x1" $ dbs $ apl (var "eval") (var "x1"))
  (lambda "x1" $ dbl $ apl (var "eval") (var "x1"))
  -- (lambda "x1" $ dbl $ apl (var "eval") $ apl2 mshift mdb0 (var "x1"))
  -- (lambda "x1" $ dbl $ apl (var "eval") (apl munshift (var "x1")))
  (lambda "x1" $ lambda "y1" $ apl (apl (var "eval") (var "x1")) (apl (var "eval") (var "y1")))
  (lambda "x1" $ lambda "y1" $ ltr (apl (var "eval") (var "x1")) (apl (var "eval") (var "y1")))

{-
 meval1 = lambda "eval" $ lambda "x" $ apl7 (var "x")
  axm
  smb1
  sdb0
  (lambda "x1" $ dbs $ apl (var "eval") (var "x1"))
  (lambda "x1" $ lbd sdb0 $ apl (var "eval") (var "x1"))
  (lambda "x1" $ lambda "y1" $ apl (apl (var "eval") (var "x1")) (apl (var "eval") (var "y1")))
  (lambda "x1" $ lambda "y1" $ ltr (apl (var "eval") (var "x1")) (apl (var "eval") (var "y1")))
-}

 -- meval = fix meval1

 meva1 = lambda "eva" $ lambda "x" $ lambda "u" $ apl7 (var "x")
  axm
  smb1 
  (var "u")
  (lambda "x1" $ dbs $ apl2 (var "eva") (var "x1") (var "u"))
  (lambda "x1" $ dbl $ apl2 (var "eva") (var "x1") db0)
  (lambda "x1" $ lambda "y1" $ apl (apl2 (var "eva") (var "x1") (var "u")) (apl2 (var "eva") (var "y1") (var "u")))
  (lambda "x1" $ lambda "y1" $ ltr (apl2 (var "eva") (var "x1") (var "u")) (apl2 (var "eva") (var "y1") (var "u")))

 meva = fix meva1

 meval = lambda "x" $ apl2 meva (var "x") (dbs db0)

{-
 mevasub = fix $ lambda "evasub" $ lambda "u" $ lambda "a" $ lambda "x" $ 
  apl4 mequal (var "u") (var "a")
   -- eval x
   (apl7 (var "x")
     axm
     smb1
     (dbs $ dbs $ dbs $ dbs $ dbs db0)
     (lambda "x1" $ dbs $ apl3 (var "evasub") mdb0 mdb0 (var "x1"))
     (lambda "x1" $ dbl $ apl3 (var "evasub") mdb0 mdb0 (var "x1"))
     (lambda "x1" $ lambda "y1" $ apl (apl3 (var "evasub") mdb0 mdb0 (var "x1"))
                                      (apl3 (var "evasub") mdb0 mdb0 (var "y1")) )
     (lambda "x1" $ lambda "y1" $ ltr (apl3 (var "evasub") mdb0 mdb0 (var "x1"))
                                      (apl3 (var "evasub") mdb0 mdb0 (var "y1")) ) )
   (apl7 (var "a")
     axm
     smb1
     (dbs $ dbs $ dbs $ dbs $ dbs db0)
     (lambda "a1" $ 
      apl4 mequal (var "u") (var "a1") 
       (apl3 (var "evasub") mdb0 mdb0 (var "u")) 
       (dbs $ apl3 (var "evasub") (var "u") (var "a1") (var "x")) )
     (lambda "a1" $
      dbl $ apl3 (var "evasub") (apl mdbs (var "u")) (var "a1") (apl2 mshift (var "u") (var "x")) )
     (lambda "a1" $ lambda "a2" $ apl (apl3 (var "evasub") (var "u") (var "a1") (var "x"))
                                      (apl3 (var "evasub") (var "u") (var "a2") (var "x")) )
     (lambda "a1" $ lambda "a2" $ ltr (apl3 (var "evasub") (var "u") (var "a1") (var "x"))
                                      (apl3 (var "evasub") (var "u") (var "a2") (var "x")) ) )
-}

 mevasub = fix $ lambda "evasub" $ lambda "u" $ lambda "a" $ lambda "x" $ 
  apl4 mequal (var "u") (var "a")
   -- eval x
   (apl7 (var "x")
     axm
     smb1
     (dbs $ dbs $ dbs $ dbs $ dbs db0)
     (lambda "x1" $ dbs $ apl3 (var "evasub") mdb0 mdb0 (var "x1"))
     (lambda "x1" $ dbl $ apl3 (var "evasub") (apl mdbs mdb0) (var "x1") mdb0)
     (lambda "x1" $ lambda "y1" $ apl (apl3 (var "evasub") mdb0 mdb0 (var "x1"))
                                      (apl3 (var "evasub") mdb0 mdb0 (var "y1")) )
     (lambda "x1" $ lambda "y1" $ ltr (apl3 (var "evasub") mdb0 mdb0 (var "x1"))
                                      (apl3 (var "evasub") mdb0 mdb0 (var "y1")) ) )
   (apl7 (var "a")
     axm
     smb1
     (dbs $ dbs $ dbs $ dbs $ dbs db0)
     (lambda "a1" $ 
      apl4 mequal (var "u") (var "a1") 
       (apl3 (var "evasub") mdb0 mdb0 (var "u")) 
       (dbs $ apl3 (var "evasub") (var "u") (var "a1") (var "x")) )
     (lambda "a1" $
      dbl $ apl3 (var "evasub") (apl mdbs (var "u")) (var "a1") (apl2 mshift (var "u") (var "x")) )
--    dbl $ apl3 (var "evasub") (apl mdbs (var "u")) (var "a1") (apl2 mshift mdb0 (var "x")) ) -- test
     (lambda "a1" $ lambda "a2" $ apl (apl3 (var "evasub") (var "u") (var "a1") (var "x"))
                                      (apl3 (var "evasub") (var "u") (var "a2") (var "x")) )
     (lambda "a1" $ lambda "a2" $ ltr (apl3 (var "evasub") (var "u") (var "a1") (var "x"))
                                      (apl3 (var "evasub") (var "u") (var "a2") (var "x")) ) )


 -- u et v = representation of left and right sides of axiom
 mlrefl = lambda "u" $ lambda "v" $ apl mmapproof $ lambda "rp" $ apl meval $ apl4 mside mleftside (var "u") (var "v") (var "rp")
 mrrefl = lambda "u" $ lambda "v" $ apl mmapproof $ lambda "rp" $ apl meval $ apl4 mside mrightside (var "u") (var "v") (var "rp")
 mrefl = lambda "s" $ lambda "u" $ lambda "v" $ apl mmapproof $ lambda "rp" $ apl meval $ apl4 mside (var "s") (var "u") (var "v") (var "rp")


 -- a theory is represented by the pair ( l , r )
 -- adding reflection gives a new theory represented by ( l1, r1 )
 -- with l1 = apl2 mpair l (apl2 mlrefl rl rr)
 -- and  r1 = apl2 mpair r (apl2 mrrefl rl rr)
 -- with rl = rep l
 -- and  rr = rep r

 -- a theory is represented by l and r ( axiom l = r )
 
 lreflex l r = apl2 mlrefl (rep l) (rep r) 
 rreflex l r = apl2 mrrefl (rep l) (rep r)

 sreflex LeftSide l r = lreflex l r
 sreflex RightSide l r = rreflex l r

 laddrefl l r = apl2 mpair l (lreflex l r)
 raddrefl l r = apl2 mpair r (rreflex l r)

 -- t = ( l , r )
 addrefl t = ( laddrefl (fst t) (snd t) , raddrefl (fst t) (snd t) )

 -- t = ( l , r )
 -- l = fst t ; r = snd t
 -- t' = addrefl t = ( l1 , r1 )
 --  = ( laddrefl l0 r0 , raddrefl l0 r0 
 --  = ( apl2 mpair l (lreflex l r), 
 --      apl2 mpair r (rreflex l r) )
 --  = ( apl2 mpair l (apl2 mlrefl (rep l) (rep r)) ,
 --      apl2 mpair r (apl2 mrrefl (rep l) (rep r) )
 --  = ( apl2 mpair l (apl mmapproof $ lambda "rp" $
 --                    apl meval $ apl4 mside mleftside (rep l) (rep r) (var "rp") ) ,
 --      apl2 mpair r (apl mmapproof $ lambda "rp" $
 --                    apl meval $ apl4 mside mrightside (rep l) (rep r) (var "rp") ) )

 firp t n = if (n <= 0) then t else addrefl t

 -- mapnat f = < f 0, < f 1, < f 2, ... >>>
 -- with < a , b > = apl2 mpair a b
 
 -- a theory is represented by the pair t = < rl , rr > = apl2 mpair rl rr 
 -- where rl and rr are representations of left and right sides of axiom l and r
 -- adding reflection gives a new theory represented by < rl1 , rr1 > = apl2 mpair rl1 rr1
 -- with rl1 = representation of pair < l , mlrefl rl rr >
 -- and  rr1 = representation of pair < r , mrrefl rl rr >
 -- representation of pair < a , b > with representation of a = ra and representation of b = rb :
 -- mpair a b = dbl (apl2 db0 a b) = dbl (apl (apl db0 a) b)
 -- mrpair ra rb = apl mdbl (apl2 mapl (apl2 mapl mdb0 ra) rb)

 mrpair = lambda "ra" $ lambda "rb" $
  apl mdbl $ apl2 mapl (apl2 mapl mdb0 (var "ra")) (var "rb")
{-
 maddrefl = lambda "t" $
  apl2 mpair (apl2 mrpair (apl (var "t") mtrue)  (rep $ apl2 mlrefl (apl (var "t") mtrue) (apl (var "t") mfalse)))
             (apl2 mrpair (apl (var "t") mfalse) (rep $ apl2 mrrefl (apl (var "t") mtrue) (apl (var "t") mfalse)))
-}
 -- conversion rules Haskell function -> SLC function
 -- non recursive function definition :
 -- f x1 ... xn = ... -> mf = lambda "x1" $ ... lambda "xn" $ ...
 -- recursive function definition :
 -- f x1 ... xn = ... -> mf = fix $ lambda "x1 $ ... lambda "xn" $ ...
 -- non recursive function call :
 -- f(x1, ..., xn) ->  apln mf (var "x1") ... (var "xn")
 -- recursive call :
 -- f(x1, ..., xn) -> apln (var "f") (var "x1") ... (var "xn")
 -- axm -> maxm
 -- dbs x -> apl mdbs (var "x")
 -- apl x y -> apl2 mapl (var "x") (var "y")
 -- SLC proof :
 -- p -> rep p
 -- (x, y) -> apl2 mpair (var "x") (var "y")
 -- if x == y then ... else ... -> apl4 mequal (var "x") (var "y") ... ...

 -- laddrefl l r = apl (apl mpair l) (lreflex l r)
 --  = apl (apl mpair l) (apl (apl mlrefl (rep l)) (rep r))
 mladdrefl = lambda "l" $ lambda "r" $ 
  apl2 mapl (apl2 mapl (rep mpair) (var "l"))
            (apl2 mapl (apl2 mapl (rep mlrefl) (apl mrep (var "l"))) (apl mrep (var "r")))

 mraddrefl = lambda "l" $ lambda "r" $ 
  apl2 mapl (apl2 mapl (rep mpair) (var "l"))
            (apl2 mapl (apl2 mapl (rep mrrefl) (apl mrep (var "l"))) (apl mrep (var "r")))

 maddrefl = lambda "t" $ 
  apl2 mpair (apl2 mladdrefl (apl mfst (var "t")) (apl msnd (var "t")))
             (apl2 mraddrefl (apl mfst (var "t")) (apl msnd (var "t")))

 mrptaddrefl = fix $ lambda "rptaddrefl" $ lambda "t" $ lambda "n" $
  apl2 (var "n")
   (var "t")
   (lambda "n1" $ apl maddrefl $ apl2 (var "rptaddrefl") (var "t") (var "n1"))

{-
 mfl = lambda "l" $ lambda "r" $ lambda "n" $
  apl (lambda "tn" $ apl mfst (var "tn"))
   (apl2 mrptaddrefl (apl2 mpair (var "l") (var "r")) (var "n"))

 mfr = lambda "l" $ lambda "r" $ lambda "n" $
  apl (lambda "tn" $ apl msnd (var "tn"))
   (apl2 mrptaddrefl (apl2 mpair (var "l") (var "r")) (var "n"))
-}

 mfl = lambda "l" $ lambda "r" $ lambda "n" $
  apl mfst $
  apl2 mrptaddrefl (apl2 mpair (var "l") (var "r")) (var "n") 

 mfr = lambda "l" $ lambda "r" $ lambda "n" $
  apl msnd $
  apl2 mrptaddrefl (apl2 mpair (var "l") (var "r")) (var "n")

 mflt = lambda "t" $ lambda "n" $
  apl mfst $
  apl2 mrptaddrefl (var "t") (var "n")

 mfrt = lambda "t" $ lambda "n" $
  apl msnd $
  apl2 mrptaddrefl (var "t") (var "n")

{-
 mtw = lambda "t" $
  apl2 mpair (apl mmapnat $ lambda "n" $ apl3 mfl (apl mfst (var "t")) (apl msnd (var "t")) (var "n"))
             (apl mmapnat $ lambda "n" $ apl3 mfr (apl mfst (var "t")) (apl msnd (var "t")) (var "n"))

 mtw = lambda "t" $
  apl2 mpair (apl mmapnat $ lambda "n" $ apl3 mflt (var "t") (var "n"))
             (apl mmapnat $ lambda "n" $ apl3 mfrt (var "t") (var "n"))
-}

 mtw = lambda "t" $
  apl2 mpair (apl mmapnat $ lambda "n" $ apl mfst $ apl2 mrptaddrefl (var "t") (var "n"))
             (apl mmapnat $ lambda "n" $ apl msnd $ apl2 mrptaddrefl (var "t") (var "n"))

 -- modify mrptaddrefl and mtw by replacing maddrefl by parameter function

 mrptf = fix $ lambda "rptf" $ lambda "f" $ lambda "t" $ lambda "n" $
  apl2 (var "n")
   (var "t")
   (lambda "n1" $ apl (var "f") $ apl3 (var "rptf") (var "f") (var "t") (var "n1"))

 mtfw = lambda "f" $ lambda "t" $ 
  apl2 mpair (apl mmapnat $ lambda "n" $ apl mfst $ apl3 mrptf (var "f") (var "t") (var "n"))
             (apl mmapnat $ lambda "n" $ apl msnd $ apl3 mrptf (var "f") (var "t") (var "n"))

 mtw1 = apl mtfw maddrefl
 mtw2 = apl mtfw mtw1 -- w^2
 mtw3 = apl mtfw mtw2 -- w^3


 data Nat =
    ZeroN
  | SucN Nat

 data Ordi =
    Zero
  | Suc Ordi
  | Lim (Nat -> Ordi)

 rpt ZeroN f x = x
 rpt (SucN n) f x = rpt n f (f x)

 fixpt f x = Lim (\n -> rpt n f x)

 w = fixpt Suc Zero

{-
 tirp :: (Proof,Proof) -> Ordi -> (Proof,Proof)
 tirp t Zero = t
 tirp t (Suc x) = addrefl (tirp t x)
 tirp t (Lim f) = ...
-}

 ordZero = lambda "z" $ lambda "s" $ lambda "l" (var "z")
 ordSuc = lambda "x" $ lambda "z" $ lambda "s" $ lambda "l" $ apl (var "s") (var "x")
 ordLim = lambda "f" $ lambda "z" $ lambda "s" $ lambda "l" $ apl (var "l") (var "f")

 mrpt = fix $ lambda "rpt" $ lambda "n" $ lambda "f" $ lambda "x" $
  apl2 (var "n")
   (var "x")
   (apl3 (var "rpt") (var "n") (var "f") (apl (var "f") (var "x")))

 mfixpt = lambda "f" $ lambda "x" $ apl ordLim (lambda "n" $ apl3 mrpt (var "n") (var "f") (var "x"))

 mw = apl2 mfixpt ordSuc ordZero

 mlimt = lambda "f" $
  apl2 mpair
   (apl mmapnat $ lambda "n" $ apl mfst $ apl (var "f") (var "n"))
   (apl mmapnat $ lambda "n" $ apl msnd $ apl (var "f") (var "n"))

 mtirp = fix $ lambda "tirp" $ lambda "t" $ lambda "x" $ 
  apl3 (var "x")
   (var "t")
   (lambda "x1" $ apl maddrefl (apl2 (var "tirp") (var "t") (var "x")))
   (lambda "f" $ apl mlimt $ lambda "n" $ apl2 (var "tirp") (var "t") (apl (var "f") (var "n")))
   
   -- (lambda "f" $ apl2 mtfw (var "f") (var "t")) 
   


