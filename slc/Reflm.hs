module Reflm where

 import Slcn

 mtrue = lambda "t" $ lambda "f" $ var "t"
 mfalse = lambda "t" $ lambda "f" $ var "f"

 mpair = lambda "x" $ lambda "y" $ lambda "f" $ apl2 (var "f") (var "x") (var "y")

 combk = lambda "x" $ lambda "y" $ var "x"

 mleftside = lambda "l" $ lambda "r" $ var "l"
 mrightside = lambda "l" $ lambda "r" $ var "r"

 smb1 = smb "SMB"
 sdb0 = smb "sdb0"

-- maxm = 
--  lambda "axm" $ lambda "smb" $ lambda "db0" $ lambda "dbs" $ lambda "dbl" $ lambda "apl" $ lambda "ltr" $ 
--  var "axm"

 maxm = 
  lambda "axm" $ lambda "smb" $ lambda "db0" $ lambda "dbs" $ lambda "nxt" $ lambda "lbd" $ lambda "apl" $ lambda "ltr" $ 
  var "axm"

 msmb = 
  lambda "axm" $ lambda "smb" $ lambda "db0" $ lambda "dbs" $ lambda "nxt" $ lambda "lbd" $ lambda "apl" $ lambda "ltr" $ 
  var "smb"

 mdb0 = 
  lambda "axm" $ lambda "smb" $ lambda "db0" $ lambda "dbs" $ lambda "nxt" $ lambda "lbd" $ lambda "apl" $ lambda "ltr" $ 
  var "db0"

 mdbs = lambda "x" $ 
  lambda "axm" $ lambda "smb" $ lambda "db0" $ lambda "dbs" $ lambda "nxt" $ lambda "lbd" $ lambda "apl" $ lambda "ltr" $ 
  apl (var "dbs") (var "x")

 mnxt = lambda "x" $
  lambda "axm" $ lambda "smb" $ lambda "db0" $ lambda "dbs" $ lambda "nxt" $ lambda "lbd" $ lambda "apl" $ lambda "ltr" $ 
  apl (var "nxt") (var "x")

 mlbd = lambda "x" $ lambda "y" $ 
  lambda "axm" $ lambda "smb" $ lambda "db0" $ lambda "dbs" $ lambda "nxt" $ lambda "lbd" $ lambda "apl" $ lambda "ltr" $ 
  apl2 (var "lbd") (var "x") (var "y")

 -- mdbl = lambda "x" $
 --  lambda "axm" $ lambda "smb" $ lambda "db0" $ lambda "dbs" $ lambda "nxt" $ lambda "lbd" $ lambda "apl" $ lambda "ltr" $ 
 --  apl (var "dbl") (var "x")

 mapl = lambda "x" $ lambda "y" $ 
  lambda "axm" $ lambda "smb" $ lambda "db0" $ lambda "dbs" $ lambda "nxt" $ lambda "lbd" $ lambda "apl" $ lambda "ltr" $ 
  apl2 (var "apl") (var "x") (var "y") 

 mltr = lambda "x" $ lambda "y" $ 
  lambda "axm" $ lambda "smb" $ lambda "db0" $ lambda "dbs" $ lambda "nxt" $ lambda "lbd" $ lambda "apl" $ lambda "ltr" $ 
  apl2 (var "ltr") (var "x") (var "y")

 rep :: Proof -> Proof
 rep (Proof0 AXM) = maxm
 rep (Proof0 (SMB s)) = msmb
 rep (Proof0 DB0) = mdb0
 rep (Proof1 DBS x) = apl mdbs (rep x)
 rep (Proof1 NXT x) = apl mnxt (rep x)
 rep (Proof2 LBD x y) = apl2 mlbd (rep x) (rep y)
 -- rep (Proof1 DBL x) = apl mdbl (rep x)
 rep (Proof2 APL x y) = apl2 mapl (rep x) (rep y)
 rep (Proof2 LTR x y) = apl2 mltr (rep x) (rep y)
 rep _ = msmb

 mequal = fix $ lambda "equal" $ lambda "x" $ lambda "y" $ 
  apl8 (var "x") 

   (apl8 (var "y") mtrue  mfalse mfalse (apl combk mfalse) (apl combk mfalse) (apl combk $ apl combk mfalse) (apl combk $ apl combk mfalse) (apl combk $ apl combk mfalse))

   (apl8 (var "y") mfalse mtrue  mfalse (apl combk mfalse) (apl combk mfalse) (apl combk $ apl combk mfalse) (apl combk $ apl combk mfalse) (apl combk $ apl combk mfalse))

   (apl8 (var "y") mfalse mfalse mtrue  (apl combk mfalse) (apl combk mfalse) (apl combk $ apl combk mfalse) (apl combk $ apl combk mfalse) (apl combk $ apl combk mfalse))

   (lambda "a" $ 
    apl8 (var "y") mfalse mfalse mfalse (apl (var "equal") (var "a")) 
                                                           (apl combk mfalse) (apl combk $ apl combk mfalse) (apl combk $ apl combk mfalse) (apl combk $ apl combk mfalse))
   (lambda "a" $
    apl8 (var "y") mfalse mfalse mfalse (apl combk mfalse) (apl (var "equal") (var "a"))
                                                                              (apl combk $ apl combk mfalse) (apl combk $ apl combk mfalse) (apl combk $ apl combk mfalse))
   (lambda "x1" $ lambda "x2" $
    apl8 (var "y") mfalse mfalse mfalse (apl combk mfalse) (apl combk mfalse) 
    (lambda "y1" $ lambda "y2" $ apl2 (apl2 (var "equal") (var "x1") (var "y1")) (apl2 (var "equal") (var "x2") (var "y2")) mfalse)
                                                                                                             (apl combk $ apl combk mfalse) (apl combk $ apl combk mfalse))
   (lambda "x1" $ lambda "x2" $ 
    apl8 (var "y") mfalse mfalse mfalse (apl combk mfalse) (apl combk mfalse) (apl combk $ apl combk mfalse) 
    (lambda "y1" $ lambda "y2" $ apl2 (apl2 (var "equal") (var "x1") (var "y1")) (apl2 (var "equal") (var "x2") (var "y2")) mfalse) (apl combk $ apl combk mfalse))

   (lambda "x1" $ lambda "x2" $ 
    apl8 (var "y") mfalse mfalse mfalse (apl combk mfalse) (apl combk mfalse) (apl combk $ apl combk mfalse) (apl combk $ apl combk mfalse)
    (lambda "y1" $ lambda "y2" $ apl2 (apl2 (var "equal") (var "x1") (var "y1")) (apl2 (var "equal") (var "x2") (var "y2")) mfalse))


 mshift = fix $ lambda "shift" $ lambda "u" $ lambda "x" $ 
  apl2 (apl2 mequal (var "x") (var "u")) (apl mdbs (var "u")) $
  apl8 (var "x")
   maxm
   msmb
   mdb0
   (lambda "x1" $ apl mdbs $ apl2 (var "shift") (var "u") (var "x1"))
   (lambda "x1" $ apl mnxt $ apl2 (var "shift") (var "u") (var "x1"))
   (lambda "x1" $ lambda "x2" $ apl2 mlbd (var "x1") $ apl2 (var "shift") (apl mdbs (var "u")) (var "x2"))
   -- (lambda "x1" $ apl mdbl $ apl2 (var "shift") (apl mdbs (var "u")) (var "x1"))
   (lambda "x1" $ lambda "x2" $ apl2 mapl (apl2 (var "shift") (var "u") (var "x1")) (apl2 (var "shift") (var "u") (var "x2")))
   (lambda "x1" $ lambda "x2" $ apl2 mltr (apl2 (var "shift") (var "u") (var "x1")) (apl2 (var "shift") (var "u") (var "x2")))

 msubst = fix $ lambda "subst" $ lambda "u" $ lambda "a" $ lambda "b" $
  apl2 (apl2 mequal (var "a") (var "u")) (var "b") $
  apl8 (var "a")
   maxm
   msmb
   mdb0
   (lambda "a1" $ apl2 (apl2 mequal (var "a1") (var "u")) (var "u") $ apl mdbs $ apl3 (var "subst") (var "u") (var "a1") (var "b"))
   (lambda "a1" $ apl mnxt (apl3 (var "subst") (var "u") (var "a1") (var "b")))
   (lambda "a1" $ lambda "a2" $ apl2 mlbd (var "a1") $ apl3 (var "subst") (apl mdbs (var "u")) (var "a2") (apl2 mshift (var "u") (var "b")))
   -- (lambda "a1" $ apl mdbl $ apl3 (var "subst") (apl mdbs (var "u")) (var "a1") (apl2 mshift mdb0 (var "b")))
   (lambda "a1" $ lambda "a2" $ apl2 mapl (apl3 (var "subst") (var "u") (var "a1") (var "b")) 
                                          (apl3 (var "subst") (var "u") (var "a2") (var "b")) )
   (lambda "a1" $ lambda "a2" $ apl2 mltr (apl3 (var "subst") (var "u") (var "a1") (var "b")) 
                                          (apl3 (var "subst") (var "u") (var "a2") (var "b")) )

 mred1 = fix $ lambda "red1" $ lambda "x" $
  apl8 (var "x") 
   maxm
   msmb
   mdb0
   (lambda "x1" $ apl mdbs $ apl (var "red1") (var "x1"))
   (lambda "x1" $ apl mnxt $ apl (var "red1") (var "x1"))
   (lambda "x1" $ lambda "x2" $ apl2 mlbd (var "x1") $ apl (var "red1") (var "x2"))
   -- (lambda "x1" $ apl mdbl $ apl (var "red1") (var "x1"))
   (lambda "x1" $ lambda "x2" $ apl8 (var "x1") 
    (apl2 mapl (apl (var "red1") (var "x1")) (apl (var "red1") (var "x2")))
    (apl2 mapl (apl (var "red1") (var "x1")) (apl (var "red1") (var "x2")))
    (apl2 mapl (apl (var "red1") (var "x1")) (apl (var "red1") (var "x2")))
    (apl combk $ apl2 mapl (apl (var "red1") (var "x1")) (apl (var "red1") (var "x2")))
    (apl combk $ apl2 mapl (apl (var "red1") (var "x1")) (apl (var "red1") (var "x2")))
    (lambda "x3" $ lambda "x4" $ apl3 msubst (var "x3") (var "x4") (var "x2"))
    -- (lambda "x3" $ apl3 msubst mdb0 (var "x3") (var "x2"))
    (apl combk $ apl combk $ apl2 mapl (apl (var "red1") (var "x1")) (apl (var "red1") (var "x2")))
    (apl combk $ apl combk $ apl2 mapl (apl (var "red1") (var "x1")) (apl (var "red1") (var "x2"))))
   (lambda "x1" $ lambda "x2" $ apl2 mltr (apl (var "red1") (var "x1")) (apl (var "red1") (var "x2")))

 mred = fix $ lambda "red" $ lambda "x" $
  apl (lambda "y" $ apl2 (apl2 mequal (var "x") (var "y")) (var "x") (apl (var "red") (var "y"))) (apl mred1 (var "x"))

 mside = fix $ lambda "side" $ lambda "s" $ lambda "u" $ lambda "v" $ lambda "x" $ apl8 (var "x") 
  (apl2 (var "s") (var "u") (var "v"))
  msmb
  mdb0
  (lambda "x1" $ apl mdbs $ apl4 (var "side") (var "s") (var "u") (var "v") (var "x1"))
  (lambda "x1" $ apl mnxt $ apl4 (var "side") (var "s") (var "u") (var "v") (var "x1"))
  (lambda "x1" $ lambda "x2" $ apl2 mlbd (var "x1") $ apl4 (var "side") (var "s") (var "u") (var "v") (var "x2")) 
  -- (lambda "x1" $ apl mdbl $ apl4 (var "side") (var "s") (var "u") (var "v") (var "x1"))
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
  lambda "x" $ apl8 (var "x") 
   (apl (var "f") maxm)
   (apl (var "f") msmb)
   (apl (var "f") mdb0)
   (apl (var "mapproof") $ lambda "x1" $ apl (var "f") $ apl mdbs (var "x1"))
   (apl (var "mapproof") $ lambda "x1" $ apl (var "f") $ apl mnxt (var "x1"))
   (apl (var "mapproof") $ lambda "x1" $ apl (var "mapproof") $ lambda "x2" $
    apl (var "f") $ apl2 mlbd (var "x1") (var "x2"))
   -- (apl (var "mapproof") $ lambda "x1" $ apl (var "f") $ apl mdbl (var "x1"))
   (apl (var "mapproof") $ lambda "x1" $ apl (var "mapproof") $ lambda "x2" $
    apl (var "f") $ apl2 mapl (var "x1") (var "x2"))
   (apl (var "mapproof") $ lambda "x1" $ apl (var "mapproof") $ lambda "x2" $
    apl (var "f") $ apl2 mltr (var "x1") (var "x2"))

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

{-
 munshift = fix $ lambda "unshift" $ lambda "x" $ apl7 (var "x")
  maxm
  msmb
  mdb0
  (lambda "x1" (var "x1"))
  (lambda "x1" $ apl mdbl (apl (var "unshift") (var "x1")))
  (lambda "x1" $ lambda "y1" $ apl2 mapl (apl (var "unshift") (var "x1")) (apl (var "unshift") (var "y1")))
  (lambda "x1" $ lambda "y1" $ apl2 mltr (apl (var "unshift") (var "x1")) (apl (var "unshift") (var "y1"))) 
-}

{-
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
-}


 meval1 = lambda "eval" $ lambda "x" $ apl8 (var "x")
  axm
  smb1
  db0i
  (lambda "x1" $ dbs $ apl (var "eval") (var "x1"))
  (lambda "x1" $ nxt $ apl (var "eval") (var "x1"))
  (lambda "x1" $ lambda "y1" $ lbd (apl (var "eval") (var "x1")) (apl (var "eval") (var "y1")))
  -- (lambda "x1" $ lbd sdb0 $ apl (var "eval") (var "x1"))
  (lambda "x1" $ lambda "y1" $ apl (apl (var "eval") (var "x1")) (apl (var "eval") (var "y1")))
  (lambda "x1" $ lambda "y1" $ ltr (apl (var "eval") (var "x1")) (apl (var "eval") (var "y1")))

 meval = fix meval1

{-
 meva1 = lambda "eva" $ lambda "x" $ lambda "u" $ apl7 (var "x")
  axm
  smb1 
  (var "u")
  (lambda "x1" $ dbs $ apl2 (var "eva") (var "x1") (var "u"))
  (lambda "x1" $ dbl $ apl2 (var "eva") (var "x1") (var "u"))
  (lambda "x1" $ lambda "y1" $ apl (apl2 (var "eva") (var "x1") (var "u")) (apl2 (var "eva") (var "y1") (var "u")))
  (lambda "x1" $ lambda "y1" $ ltr (apl2 (var "eva") (var "x1") (var "u")) (apl2 (var "eva") (var "y1") (var "u")))

 meva = fix meva1
-}



