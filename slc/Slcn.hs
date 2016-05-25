module Slcn where

 import Data.List

 data Proof = Proof0 Rule0 | Proof1 Rule1 Proof | Proof2 Rule2 Proof Proof
  deriving (Eq, Show)

 data Rule0 = AXM | DB0 | SMB String
  deriving (Eq, Show)

 data Rule1 = DBS | DBL | RED | LFT | RGT | RFL
  deriving (Eq, Show)

 data Rule2 = EQU | APL | LTR | LTS | SUB
  deriving (Eq, Show)

 axm = Proof0 AXM
 db0 = Proof0 DB0
 smb s = Proof0 (SMB s)
 dbs x = Proof1 DBS x
 dbl x = Proof1 DBL x
 red x = Proof1 RED x
 lft x = Proof1 LFT x
 rgt x = Proof1 RGT x
 rfl x = Proof1 RFL x
 equ x y = Proof2 EQU x y
 apl x y = Proof2 APL x y
 ltr x y = Proof2 LTR x y
 lts x y = Proof2 LTS x y
 sub x y = Proof2 SUB x y

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
 side s a b (Proof2 LTS x y) = if (side LeftSide a b x) == (side LeftSide a b y) then (side RightSide a b (if s == LeftSide then x else y)) else Proof2 LTR x y
 side LeftSide a b (Proof2 SUB x y) = Proof2 APL (Proof1 DBL (side LeftSide a b x)) (side LeftSide a b y)
 side RightSide a b (Proof2 SUB x y) = subst (Proof0 DB0) (side RightSide a b x) (side RightSide a b y)
 side LeftSide a b (Proof1 RED x) = side LeftSide a b x
 side RightSide a b (Proof1 RED x) = reduce (side RightSide a b x)
 side _ a b (Proof1 LFT x) = side LeftSide a b x
 side _ a b (Proof1 RGT x) = side RightSide a b x
 side _ _ _ (Proof1 RFL x) = x   
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
 allan = smb "Allan"
 brenda = smb "Brenda"
 charles = smb "Charles"

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

{-
 imp = SMB "imp"
 false = SMB "false"
 al = SMB "all"
 some = SMB "some"
 p = SMB "p"

 propMp = lambda "p" $ lambda "q" $ EQU (APL (apl2 imp (var "p") (var "q")) $ APL (var "p") (var "q")) ident
 propAk = lambda "p" $ lambda "q" $ EQU (apl2 imp (var "p") (apl2 imp (var "q") (var "p"))) ident
 propAs = lambda "p" $ lambda "q" $ lambda "r" $ 
  EQU (apl2 imp (apl2 imp (var "p") (apl2 imp (var "q") (var "r"))) (apl2 imp (apl2 imp (var "p") (var "q")) (apl2 imp (var "p") (var "r")))) ident
 propEfq = lambda "p" $ EQU (apl2 imp false (var "p")) ident 
 propRaa = lambda "p" $ EQU (apl2 imp (apl2 imp (apl2 imp (var "p") false) false) (var "p")) ident
 predGen = lambda "p" $ EQU (APL (var "p") (APL al (DBL (var "p")))) ident
 predPart = lambda "p" $ lambda "t" $ EQU (apl2 imp (APL al (var "p")) (APL (var "p") (var "t"))) ident
 predPermut = lambda "p" $ lambda "q" $ EQU (apl2 imp (APL al $ lambda "x" $ apl2 imp (var "p") (APL (var "q") (var "x"))) (apl2 imp (var "p") (APL al (var "q")))) ident
 predSome = lambda "p" $ EQU (apl2 imp (apl2 imp (APL al (var "p")) false) (apl2 imp (APL (var "p") (APL some $ lambda "x" $ apl2 imp (APL (var "p") (var "x")) false)) false)) ident

 propLemma1 = apl3 propAs p (apl2 imp p p) p
 propLemma2 = apl2 propAk p (apl2 imp p p)
 propLemma3 = apl2 propMp (apl2 imp p (apl2 imp (apl2 imp p p) p)) (apl2 imp (apl2 imp p (apl2 imp p p)) (apl2 imp p p))
 propLemma4 = APL propLemma1 (APL (apl2 imp p (apl2 imp (apl2 imp p p) p)) (apl2 imp (apl2 imp p (apl2 imp p p)) (apl2 imp p p)))
 propLemma5 = LTR propLemma4 propLemma3
 propLemma6 = APL propLemma2 (apl2 imp (apl2 imp p (apl2 imp p p)) (apl2 imp p p))
 propLemma7 = LTR propLemma6 propLemma5
 propLemma8 = apl2 propAk p p
 propLemma9 = apl2 propMp (apl2 imp p (apl2 imp p p)) (apl2 imp p p)
 propLemma10 = APL propLemma7 (APL (apl2 imp p (apl2 imp p p)) (apl2 imp p p))
 propLemma11 = LTR propLemma10 propLemma9
 propLemma12 = APL propLemma8 (apl2 imp p p)
 -- propTheorem1 = LTR propLemma12 propLemma11
 propLemma13 = LTR propLemma12 propLemma12
 propLemma14 = LTR propLemma12 propLemma11
 propTheorem1 = LTR propLemma13 propLemma14 
-}

 test = do
  proves (ltr (ltr axm (smb "SMB")) (apl (smb "SMB") axm))
  proves (ltr (ltr axm (smb "SMB")) (apl axm (smb "SMB")))
  proves (ltr (ltr axm (smb "SMB")) (apl axm axm))
  reducesTo (apl (apl (dbl db0) (dbl db0)) (apl (dbl db0) (smb "SMB")))
  reducesTo (fix ident)
  reducesTo (fix (dbl (apl (smb "SMB") db0)))  
  proves gpTheorem1c
  -- proves propTheorem1

