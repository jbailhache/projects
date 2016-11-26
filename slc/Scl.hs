module Scl where

 import Data.List
 import Data.Char

 data Proof = Proof0 Rule0 | Proof1 Rule1 Proof | Proof2 Rule2 Proof Proof
  deriving (Eq)

 data Rule0 = AXM | SMB String | CBI | CBK | CBS
  deriving (Eq, Show)

 data Rule1 = NOP
  deriving (Eq, Show)

 data Rule2 = APL | LTR
  deriving (Eq, Show)

 axm = Proof0 AXM
 smb s = Proof0 (SMB s)
 cbi = Proof0 CBI
 cbk = Proof0 CBK
 cbs = Proof0 CBS
 nop x = Proof1 NOP x
 apl x y = Proof2 APL x y
 ltr x y = Proof2 LTR x y

 instance Show Proof where
  show (Proof0 (SMB s)) = s
  show (Proof0 r) = map toLower(show r) 
  show (Proof1 r x) = "(" ++ map toLower(show r) ++ " " ++ show x ++ ")"
  show (Proof2 r x y) = "(" ++ map toLower(show r) ++ " " ++ show x ++ " " ++ show y ++ ")"


 data Side = LeftSide | RightSide 
  deriving (Eq, Show)

 switchside LeftSide u v = u
 switchside RightSide u v = v


 cont :: Proof -> Proof -> Bool
 cont1 :: Proof -> Proof -> Bool
 cont x y = if x == y then True else cont1 x y
 cont1 (Proof0 r) _ = False
 cont1 (Proof1 r x) y = cont x y
 cont1 (Proof2 r x y) z = (cont x z) || (cont y z) 

 red1 :: Proof -> Proof
 red1 (Proof2 APL (Proof0 CBI) x) = x
 red1 (Proof2 APL (Proof2 APL (Proof0 CBK) x) y) = x
 red1 (Proof2 APL (Proof2 APL (Proof2 APL (Proof0 CBS) x) y) z) = Proof2 APL (Proof2 APL x z) (Proof2 APL y z)
 red1 (Proof0 r) = Proof0 r
 red1 (Proof1 r x) = Proof1 r (red1 x)
 red1 (Proof2 r x y) = Proof2 r (red1 x) (red1 y)

 red2 :: [Proof] -> [Proof]
 red2 [] = []
 red2 (x : l) = (red1 x) : (x : l)

 red3 :: [Proof] -> [Proof]
 red3 [] = []
 -- red3 (x : l) = if elem x l then (x : l) else red3 (red2 (x : l))
 red3 (x : l) = case find (\y -> cont x y) l of
	Nothing -> red3 (red2 (x : l))
	Just _ -> x : l

 reduce :: Proof -> Proof
 reduce x = case red3 (x : []) of
		[] -> x
		y : m -> y
 -- reduce x = if red1 x == x then x else reduce (red1 x)

 rered1 :: Int -> Proof -> Proof
 rered1 n x = if (n == 0) then x else rered1 (n - 1) (red1 x)

 side :: Side -> Proof -> Proof -> Proof -> Proof
 -- AXM |- u = v
 side LeftSide u v (Proof0 AXM) = u
 -- LTR : a = b, c = d |- if reduce(a) == reduce(c) then reduce(b) = reduce(d)  
 side s u v (Proof2 LTR x y) =
	if reduce (side LeftSide u v x) == reduce (side LeftSide u v y) 
	then reduce (side RightSide u v (if s == LeftSide then x else y)) 
    else Proof2 LTR x y
 -- NOP : a = b |- a = b
 -- NOP x = x
 side s u v (Proof1 NOP x) = side s u v x
 side _ _ _ (Proof0 r) = Proof0 r
 side s u v (Proof1 r x) = Proof1 r (side s u v x)
 side s u v (Proof2 r x y) = Proof2 r (side s u v x) (side s u v y)


 apl2 :: Proof -> Proof -> Proof -> Proof
 apl2 f x1 x2 = apl (apl f x1) x2

 apl3 :: Proof -> Proof -> Proof -> Proof -> Proof
 apl3 f x1 x2 x3 = apl (apl (apl f x1) x2) x3

 apl4 :: Proof -> Proof -> Proof -> Proof -> Proof -> Proof
 apl4 f x1 x2 x3 x4 = apl (apl (apl (apl f x1) x2) x3) x4

 apl5 :: Proof -> Proof -> Proof -> Proof -> Proof -> Proof -> Proof
 apl5 f x1 x2 x3 x4 x5 = apl (apl (apl (apl (apl f x1) x2) x3) x4) x5

 apl6 :: Proof -> Proof -> Proof -> Proof -> Proof -> Proof -> Proof -> Proof
 apl6 f x1 x2 x3 x4 x5 x6 = apl (apl (apl (apl (apl (apl f x1) x2) x3) x4) x5) x6

 apl7 :: Proof -> Proof -> Proof -> Proof -> Proof -> Proof -> Proof -> Proof -> Proof
 apl7 f x1 x2 x3 x4 x5 x6 x7 = apl (apl (apl (apl (apl (apl (apl f x1) x2) x3) x4) x5) x6) x7


 var :: String -> Proof
 var x = Proof0 (SMB x)

 contSmb :: Proof -> String -> Bool
 contSmb (Proof0 (SMB s1)) s2 = s1 == s2
 contSmb (Proof0 r) _ = False
 contSmb (Proof1 r x) s = contSmb x s
 contSmb (Proof2 r x y) s = (contSmb x s) || (contSmb y s)

 lambda :: String -> Proof -> Proof
 lambda v (Proof0 (SMB s)) = if v == s then cbi else apl cbk (smb s)
 lambda v (Proof2 APL x y) = apl2 cbs (lambda v x) (lambda v y)
 lambda v (Proof2 LTR x y) = ltr (lambda v x) (lambda v y)
 lambda v x = apl cbk x


 a = smb "a"
 b = smb "b"
 c = smb "c"
 d = smb "d"


 ident = lambda "x" (var "x")
 auto = lambda "x" (apl (var "x") (var "x"))
 comp f g = lambda "x" (apl f (apl g (var "x")))
 fix f = apl auto (comp f auto)
 

 mtrue = lambda "t" $ lambda "f" $ var "t"
 mfalse = lambda "t" $ lambda "f" $ var "f"

 mpair = lambda "x" $ lambda "y" $ lambda "f" $ apl2 (var "f") (var "x") (var "y")

 combi = cbi
 combk = cbk
 combs = cbs

 mleftside = lambda "l" $ lambda "r" $ var "l"
 mrightside = lambda "l" $ lambda "r" $ var "r"


 smb1 = smb "SMB"


 caxm =
  lambda "axm" $ lambda "smb" $ lambda "cbi" $ lambda "cbk" $ lambda "cbs" $ lambda "apl" $ lambda "ltr" $
  var "axm"

 csmb =
  lambda "axm" $ lambda "smb" $ lambda "cbi" $ lambda "cbk" $ lambda "cbs" $ lambda "apl" $ lambda "ltr" $
  var "smb"

 ccbi =
  lambda "axm" $ lambda "smb" $ lambda "cbi" $ lambda "cbk" $ lambda "cbs" $ lambda "apl" $ lambda "ltr" $
  var "cbi"

 ccbk =
  lambda "axm" $ lambda "smb" $ lambda "cbi" $ lambda "cbk" $ lambda "cbs" $ lambda "apl" $ lambda "ltr" $
  var "cbk"

 ccbs =
  lambda "axm" $ lambda "smb" $ lambda "cbi" $ lambda "cbk" $ lambda "cbs" $ lambda "apl" $ lambda "ltr" $
  var "cbs"

 capl = lambda "x" $ lambda "y" $
  lambda "axm" $ lambda "smb" $ lambda "cbi" $ lambda "cbk" $ lambda "cbs" $ lambda "apl" $ lambda "ltr" $
  apl2 (var "apl") (var "x") (var "y")

 cltr = lambda "x" $ lambda "y" $
  lambda "axm" $ lambda "smb" $ lambda "cbi" $ lambda "cbk" $ lambda "cbs" $ lambda "apl" $ lambda "ltr" $
  apl2 (var "ltr") (var "x") (var "y")


 mequal = fix $ lambda "equal" $ lambda "x" $ lambda "y" $ apl7 (var "x")
  (apl7 (var "y") mtrue  mfalse mfalse mfalse mfalse (apl combk $ apl combk mfalse) (apl combk $ apl combk mfalse))
  (apl7 (var "y") mfalse mtrue  mfalse mfalse mfalse (apl combk $ apl combk mfalse) (apl combk $ apl combk mfalse))
  (apl7 (var "y") mfalse mfalse mtrue  mfalse mfalse (apl combk $ apl combk mfalse) (apl combk $ apl combk mfalse))
  (apl7 (var "y") mfalse mfalse mfalse mtrue  mfalse (apl combk $ apl combk mfalse) (apl combk $ apl combk mfalse))
  (apl7 (var "y") mfalse mfalse mfalse mfalse mtrue  (apl combk $ apl combk mfalse) (apl combk $ apl combk mfalse))
  (lambda "x1" $ lambda "x2" $
   apl7 (var "y") mfalse mfalse mfalse mfalse mfalse 
   (lambda "y1" $ lambda "y2" $ apl2 (apl2 (var "equal") (var "x1") (var "y1")) (apl2 (var "equal") (var "x2") (var "y2")) mfalse)
                                                                                                             (apl combk $ apl combk mfalse))
  (lambda "x1" $ lambda "x2" $ 
   apl7 (var "y") mfalse mfalse mfalse mfalse mfalse (apl combk $ apl combk mfalse) 
   (lambda "y1" $ lambda "y2" $ apl2 (apl2 (var "equal") (var "x1") (var "y1")) (apl2 (var "equal") (var "x2") (var "y2")) mfalse))

 rep :: Proof -> Proof
 rep (Proof0 AXM) = caxm
 rep (Proof0 (SMB s)) = csmb
 rep (Proof0 CBI) = ccbi
 rep (Proof0 CBK) = ccbk
 rep (Proof0 CBS) = ccbs
 rep (Proof1 NOP x) = rep x
 rep (Proof2 APL x y) = apl2 capl (rep x) (rep y)
 rep (Proof2 LTR x y) = apl2 cltr (rep x) (rep y)

 mred1 = fix $ lambda "red1" $ lambda "x" $ apl7 (var "x")
  caxm
  csmb
  ccbi
  ccbk
  ccbs
  (lambda "x1" $ lambda "x2" $ apl7 (var "x1")
   (apl2 capl caxm (apl (var "red1") (var "x1")))
   (apl2 capl csmb (apl (var "red1") (var "x1")))
   (var "x1")
   (apl2 capl ccbk (apl (var "red1") (var "x1")))
   (apl2 capl ccbs (apl (var "red1") (var "x1")))
   (lambda "x3" $ lambda "x4" $ apl7 (var "x3")
    (apl2 capl (apl2 capl caxm (apl (var "red1") (var "x4"))) (apl (var "red1") (var "x2")))
    (apl2 capl (apl2 capl csmb (apl (var "red1") (var "x4"))) (apl (var "red1") (var "x2")))
    (apl2 capl (var "x4") (var "x2"))
    (var "x4")
    (apl2 capl (apl2 capl ccbs (apl (var "red1") (var "x4"))) (apl (var "red1") (var "x2")))
    (lambda "x5" $ lambda "x6" $ apl7 (var "x5")
     (apl2 capl (apl2 capl (apl2 capl caxm (apl (var "red1") (var "x6"))) (apl (var "red1") (var "x4"))) (apl (var "red1") (var "x2")))
     (apl2 capl (apl2 capl (apl2 capl csmb (apl (var "red1") (var "x6"))) (apl (var "red1") (var "x4"))) (apl (var "red1") (var "x2")))
     (apl2 capl (apl2 capl (var "x6") (var "x4")) (var "x2"))
     (apl2 capl (var "x6") (var "x2"))
     (apl2 capl (apl2 capl (var "x6") (var "x2")) (apl2 capl (var "x4") (var "x2")))
     (lambda "x7" $ lambda "x8" $
      apl2 capl (apl2 capl (apl2 capl (apl2 capl (apl (var "red1") (var "x7")) (apl (var "red1") (var "x8"))) (apl (var "red1") (var "x6"))) (apl (var "red1") (var "x4"))) (apl (var "red1") (var "x2")))
     (lambda "x7" $ lambda "x8" $
      apl2 capl (apl2 capl (apl2 capl (apl2 cltr (apl (var "red1") (var "x7")) (apl (var "red1") (var "x8"))) (apl (var "red1") (var "x6"))) (apl (var "red1") (var "x4"))) (apl (var "red1") (var "x2"))))
    (lambda "x5" $ lambda "x6" $
     apl2 capl (apl2 capl (apl2 cltr (apl (var "red1") (var "x5")) (apl (var "red1") (var "x6"))) (apl (var "red1") (var "x4"))) (apl (var "red1") (var "x2"))))
   (lambda "x3" $ lambda "x4" $ apl2 capl (apl2 cltr (apl (var "red1") (var "x3")) (apl (var "red1") (var "x4"))) (apl (var "red1") (var "x2"))))
  (lambda "x1" $ lambda "x2" $ apl2 cltr (apl (var "red1") (var "x1")) (apl (var "red1") (var "x2")))

 mred = fix $ lambda "red" $ lambda "x" $
  apl (lambda "y" $ apl2 (apl2 mequal (var "x") (var "y")) (var "x") (apl (var "red") (var "y"))) (apl mred1 (var "x"))


 mside = fix $ lambda "side" $ lambda "s" $ lambda "u" $ lambda "v" $ lambda "x" $ apl7 (var "x") 
  (apl2 (var "s") (var "u") (var "v"))
  csmb
  ccbi
  ccbk
  ccbs
  (lambda "x1" $ lambda "x2" $ apl2 capl (apl4 (var "side") (var "s") (var "u") (var "v") (var "x1"))
                                         (apl4 (var "side") (var "s") (var "u") (var "v") (var "x2")))
  (lambda "x1" $ lambda "x2" $ 
   apl2 (apl2 mequal (apl mred $ apl4 (var "side") mleftside (var "u") (var "v") (var "x1"))
                     (apl mred $ apl4 (var "side") mleftside (var "u") (var "v") (var "x2")))
    (apl mred $ apl4 (var "side") mrightside (var "u") (var "v") (apl2 (var "s") (var "x1") (var "x2")))
    (apl2 cltr (var "x1") (var "x2")))


 meval1 = lambda "eval" $ lambda "x" $ apl7 (var "x")
  axm
  smb1
  cbi
  cbk
  cbs
  (lambda "x1" $ lambda "x2" $ apl (apl (var "eval") (var "x1")) (apl (var "eval") (var "x2")))
  (lambda "x1" $ lambda "x2" $ ltr (apl (var "eval") (var "x1")) (apl (var "eval") (var "x2")))

 meval = fix meval1


 -- mapproof f = f axm
 -- mapproof f = f smb1
 mapproof f = apl2 mpair (f axm) (f smb1)
 -- mapproof f = lambda "g" $ apl2 (var "g") (f axm) (f smb1) 
 -- mapproof f = lambda "g" $ apl f (apl2 (var "g") maxm msmb)


 mmapproof = fix $ lambda "mapproof" $ lambda "f" $
  lambda "x" $ apl7 (var "x") 
   (apl (var "f") caxm)
   (apl (var "f") csmb)
   (apl (var "f") ccbi)
   (apl (var "f") ccbk)
   (apl (var "f") ccbs)
   (apl (var "mapproof") $ lambda "x1" $ apl (var "mapproof") $ lambda "x2" $
    apl (var "f") $ apl2 capl (var "x1") (var "x2"))
   (apl (var "mapproof") $ lambda "x1" $ apl (var "mapproof") $ lambda "x2" $
    apl (var "f") $ apl2 cltr (var "x1") (var "x2"))

 refl s u v = apl2 mpair (switchside s u v) (mapproof (side s u v))
 -- refl s u v = apl2 mpair (switchside s u v) (mapproof $ lambda "x" $ apl4 mside (switchside s mleftside mrightside) (rep u) (rep v) (var "x"))


