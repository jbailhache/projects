module Slcn where

 import Data.List
 import Data.Char

 data Proof = Proof0 Rule0 | Proof1 Rule1 Proof | Proof2 Rule2 Proof Proof
  deriving (Eq)

 data Rule0 = AXM | DB0 | SMB String
  deriving (Eq, Show)

 data Rule1 = DBS | DBL | RED | RD2 | RDR | LFT | RGT | RFL | EVL | EVR
  deriving (Eq, Show)

 data Rule2 = EQU | APL | LTR | LT2 | LTS | SUB
  deriving (Eq, Show)

 axm = Proof0 AXM
 db0 = Proof0 DB0
 smb s = Proof0 (SMB s)
 dbs x = Proof1 DBS x
 dbl x = Proof1 DBL x
 red x = Proof1 RED x
 rd2 x = Proof1 RD2 x
 rdr x = Proof1 RDR x
 lft x = Proof1 LFT x
 rgt x = Proof1 RGT x
 rfl x = Proof1 RFL x
 evl x = Proof1 EVL x
 evr x = Proof1 EVR x
 equ x y = Proof2 EQU x y
 apl x y = Proof2 APL x y
 ltr x y = Proof2 LTR x y
 lt2 x y = Proof2 LT2 x y
 lts x y = Proof2 LTS x y
 sub x y = Proof2 SUB x y

 instance Show Proof where
  show (Proof0 (SMB s)) = s
  show (Proof0 r) = map toLower(show r) 
  show (Proof1 r x) = "(" ++ map toLower(show r) ++ " " ++ show x ++ ")"
  show (Proof2 r x y) = "(" ++ map toLower(show r) ++ " " ++ show x ++ " " ++ show y ++ ")"

 data Side = LeftSide | RightSide
  deriving (Eq, Show)

 shift :: Proof -> Proof -> Proof
 shift u (Proof1 DBS x) = if u == Proof1 DBS x then Proof1 DBS u else Proof1 DBS (shift u x)
 shift u (Proof1 DBL x) = Proof1 DBL (shift (Proof1 DBS u) x)
 shift _ (Proof0 r) = Proof0 r
 shift u (Proof1 r x) = Proof1 r (shift u x)
 shift u (Proof2 r x y) = Proof2 r (shift u x) (shift u y)

 subst :: Proof -> Proof -> Proof -> Proof
 subst1 :: Proof -> Proof -> Proof -> Proof
 subst u a b = if u == a then b else (if Proof1 DBS u == a then u else subst1 u a b)
 subst1 u (Proof1 DBL x) b = Proof1 DBL (subst (Proof1 DBS u) x (shift (Proof0 DB0) b))
 subst1 _ (Proof0 r) _ = Proof0 r
 subst1 u (Proof1 r x) b = Proof1 r (subst u x b)
 subst1 u (Proof2 r x y) b = Proof2 r (subst u x b) (subst u y b)

 cont :: Proof -> Proof -> Bool
 cont1 :: Proof -> Proof -> Bool
 cont x y = if x == y then True else cont1 x y
 cont1 (Proof0 r) _ = False
 cont1 (Proof1 r x) y = cont x y
 cont1 (Proof2 r x y) z = (cont x z) || (cont y z) 

 red1 :: Proof -> Proof
 red1 (Proof2 APL (Proof1 DBL x) y) = subst (Proof0 DB0) x y
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

 side :: Side -> Proof -> Proof -> Proof -> Proof
 side LeftSide a b (Proof0 AXM) = a
 side RightSide a b (Proof0 AXM) = b
 side LeftSide _ _ (Proof2 EQU x y) = x
 side RightSide _ _ (Proof2 EQU x y) = y
 side s a b (Proof2 LTR x y) = 
	let lx = side LeftSide a b x
	    ly = side LeftSide a b y
	in let rlx = reduce lx
	       rly = reduce ly
	   in if (lx == ly) || (lx == rly) || (rlx == ly) || (rlx == rly) 
	      -- then reduce (side RightSide a b (if s == LeftSide then x else y))
          then (if s == LeftSide then (side RightSide a b x) else reduce (side RightSide a b y))
	      else Proof2 LTR x y

 side s a b (Proof2 LT2 x y) = 
	let lx = side LeftSide a b x
	    ly = side LeftSide a b y
	in let rlx = reduce lx
	       rly = reduce ly
	   in if (lx == ly) || (lx == rly) || (rlx == ly) || (rlx == rly) 
	      then reduce (side RightSide a b (if s == LeftSide then x else y))
          -- then (if s == LeftSide then (side RightSide a b x) else reduce (side RightSide a b y))
	      else Proof2 LT2 x y
 side s a b (Proof2 LTS x y) = if (side LeftSide a b x) == (side LeftSide a b y) then (side RightSide a b (if s == LeftSide then x else y)) else Proof2 LTR x y
 side LeftSide a b (Proof2 SUB x y) = Proof2 APL (Proof1 DBL (side LeftSide a b x)) (side LeftSide a b y)
 side RightSide a b (Proof2 SUB x y) = subst (Proof0 DB0) (side RightSide a b x) (side RightSide a b y)
 side LeftSide a b (Proof1 RED x) = side LeftSide a b x
 side RightSide a b (Proof1 RED x) = reduce (side RightSide a b x)
 side s a b (Proof1 RD2 x) = reduce (side s a b x)
 side LeftSide a b (Proof1 RDR x) = x
 side RightSide a b (Proof1 RDR x) = reduce x
 side _ a b (Proof1 LFT x) = side LeftSide a b x
 side _ a b (Proof1 RGT x) = side RightSide a b x
 side _ _ _ (Proof1 RFL x) = x   
 side s a b (Proof1 EVL x) = side s a b (side LeftSide a b x)
 side s a b (Proof1 EVR x) = side s a b (side RightSide a b x)
 side _ _ _ (Proof0 r) = Proof0 r
 side s a b (Proof1 r x) = Proof1 r (side s a b x)
 side s a b (Proof2 r x y) = Proof2 r (side s a b x) (side s a b y)

 var :: String -> Proof
 var x = Proof0 (SMB x)

 contSmb :: Proof -> String -> Bool
 contSmb (Proof0 (SMB s1)) s2 = s1 == s2
 contSmb (Proof0 r) _ = False
 contSmb (Proof1 r x) s = contSmb x s
 contSmb (Proof2 r x y) s = (contSmb x s) || (contSmb y s)
 
 abstr :: Proof -> String -> Proof -> Proof
 abstr1 :: Proof -> String -> Proof -> Proof
 abstr d v x = if (contSmb x v) then (abstr1 d v x) else x
 abstr1 d v (Proof0 (SMB s)) = if v == s then d else (Proof0 (SMB s))
 abstr1 d v (Proof1 DBL x) = Proof1 DBL (abstr (Proof1 DBS d) v x)
 abstr1 _ _ (Proof0 r) = Proof0 r
 abstr1 d v (Proof1 r x) = Proof1 r (abstr d v x)
 abstr1 d v (Proof2 r x y) = Proof2 r (abstr d v x) (abstr d v y)

 lambda :: String -> Proof -> Proof
 lambda v x = Proof1 DBL (abstr (Proof0 DB0) v x)

 apl2 :: Proof -> Proof -> Proof -> Proof
 apl2 f x1 x2 = apl (apl f x1) x2

 apl3 :: Proof -> Proof -> Proof -> Proof -> Proof
 apl3 f x1 x2 x3 = apl (apl (apl f x1) x2) x3

 axl = smb "SMB"
 axr = apl (smb "SMB") (smb "SMB")

 left = side LeftSide axl axr
 right = side RightSide axl axr

 proves x = do
  putStr ("\nThe proof\n  " ++ show x ++ " \nproves\n  " ++ show (left x) ++ "\n= " ++ show (right x) ++ "\n")

 reducesTo x = do
  putStr ("\n  " ++ show x ++ "\nreduces to\n  " ++ show (reduce x) ++ "\n")

 ident = dbl db0
 auto = dbl (apl db0 db0)
 comp f g = dbl (apl f (apl g db0))
 fix f = apl auto (comp f auto)
 ias = fix (dbl (apl (smb "SMB") db0))

 parent = smb "parent"
 gdparent = smb "gdparent"
 allan = smb "allan"
 brenda = smb "brenda"
 charles = smb "charles"

 gpRule1 = lambda "x" $ lambda "y" $ lambda "z" $ 
  equ (apl (apl2 parent (var "x") (var "y")) $
       apl (apl2 parent (var "y") (var "z")) $
       apl2 gdparent (var "x") (var "z"))
      ident
 gpAxiom1 = equ (apl2 parent allan brenda) ident
 gpAxiom2 = equ (apl2 parent brenda charles) ident

 gpLemma1c = apl3 gpRule1 allan brenda charles
 gpLemma2c = apl gpAxiom1 $ apl (apl2 parent brenda charles) $ apl2 gdparent allan charles
 gpLemma3c = ltr gpLemma2c gpLemma1c
 gpLemma4c = apl gpAxiom2 $ apl2 gdparent allan charles
 gpLemma5c = ltr gpLemma4c gpLemma3c
 gpLemma6c = ltr gpLemma4c gpLemma4c
 gpTheorem1c = ltr gpLemma6c gpLemma5c


 imp = smb "imp"
 false = smb "false"
 al = smb "all"
 some = smb "some"
 p = smb "p"

 propMp = lambda "p" $ lambda "q" $ equ (apl (apl2 imp (var "p") (var "q")) $ apl (var "p") (var "q")) ident
 propAk = lambda "p" $ lambda "q" $ equ (apl2 imp (var "p") (apl2 imp (var "q") (var "p"))) ident
 propAs = lambda "p" $ lambda "q" $ lambda "r" $ 
  equ (apl2 imp (apl2 imp (var "p") (apl2 imp (var "q") (var "r"))) (apl2 imp (apl2 imp (var "p") (var "q")) (apl2 imp (var "p") (var "r")))) ident
 propEfq = lambda "p" $ equ (apl2 imp false (var "p")) ident 
 propRaa = lambda "p" $ equ (apl2 imp (apl2 imp (apl2 imp (var "p") false) false) (var "p")) ident
 predGen = lambda "p" $ equ (apl (var "p") (apl al (dbl (var "p")))) ident
 predPart = lambda "p" $ lambda "t" $ equ (apl2 imp (apl al (var "p")) (apl (var "p") (var "t"))) ident
 predPermut = lambda "p" $ lambda "q" $ equ (apl2 imp (apl al $ lambda "x" $ apl2 imp (var "p") (apl (var "q") (var "x"))) (apl2 imp (var "p") (apl al (var "q")))) ident
 predSome = lambda "p" $ equ (apl2 imp (apl2 imp (apl al (var "p")) false) (apl2 imp (apl (var "p") (apl some $ lambda "x" $ apl2 imp (apl (var "p") (var "x")) false)) false)) ident

 propLemma1 = apl3 propAs p (apl2 imp p p) p
 propLemma2 = apl2 propAk p (apl2 imp p p)
 propLemma3 = apl2 propMp (apl2 imp p (apl2 imp (apl2 imp p p) p)) (apl2 imp (apl2 imp p (apl2 imp p p)) (apl2 imp p p))
 propLemma4 = apl propLemma1 (apl (apl2 imp p (apl2 imp (apl2 imp p p) p)) (apl2 imp (apl2 imp p (apl2 imp p p)) (apl2 imp p p)))
 propLemma5 = ltr propLemma4 propLemma3
 propLemma6 = apl propLemma2 (apl2 imp (apl2 imp p (apl2 imp p p)) (apl2 imp p p))
 propLemma7 = ltr propLemma6 propLemma5
 propLemma8 = apl2 propAk p p
 propLemma9 = apl2 propMp (apl2 imp p (apl2 imp p p)) (apl2 imp p p)
 propLemma10 = apl propLemma7 (apl (apl2 imp p (apl2 imp p p)) (apl2 imp p p))
 propLemma11 = ltr propLemma10 propLemma9
 propLemma12 = apl propLemma8 (apl2 imp p p)
 -- propTheorem1 = LTR propLemma12 propLemma11
 propLemma13 = ltr propLemma12 propLemma12
 propLemma14 = ltr propLemma12 propLemma11
 propTheorem1 = ltr propLemma13 propLemma14 

 a = smb "a"
 b = smb "b"
 c = smb "c"

 ltr2 = dbl (dbl (ltr (ltr (dbs db0) (dbs db0)) (ltr (dbs db0) db0))) 

 test = do
  proves (ltr (ltr axm (smb "SMB")) (apl (smb "SMB") axm))
  proves (ltr (ltr axm (smb "SMB")) (apl axm (smb "SMB")))
  proves (ltr (ltr axm (smb "SMB")) (apl axm axm))
  reducesTo (apl (apl (dbl db0) (dbl db0)) (apl (dbl db0) (smb "SMB")))
  reducesTo (fix ident)
  reducesTo (fix (dbl (apl (smb "SMB") db0)))  
  proves gpTheorem1c
  proves propTheorem1
  proves (red (equ (apl (dbl db0) a) (apl (dbl db0) b)))
  proves (rdr (equ (apl (dbl db0) a) (apl (dbl db0) b)))
  proves (red (rfl (equ (apl (dbl db0) a) (apl (dbl db0) b))))
  proves (evr (rdr (apl (apl (dbl (dbl (ltr (ltr (dbs db0) (dbs db0)) (ltr (dbs db0) db0)))) gpLemma4c) gpLemma3c)))
  proves (evr (red (rfl (apl (apl (dbl (dbl (ltr (ltr (dbs db0) (dbs db0)) (ltr (dbs db0) db0)))) gpLemma4c) gpLemma3c))))
  proves (evr $ red $ rfl $ apl2 ltr2 gpLemma4c gpLemma3c)
  proves (lt2 gpLemma4c gpLemma3c)

