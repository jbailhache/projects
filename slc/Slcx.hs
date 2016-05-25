module Slcx where
 
 import Data.List

 data Proof = AXM
            | EQU Proof Proof
            | SMB String
            | DB0 
            | DBS Proof
            | DBL Proof
            | APL Proof Proof
            | LTR Proof Proof
            | LTS Proof Proof
            | SUB Proof Proof
            | RED Proof
            | LFT Proof
            | RGT Proof
            | RFL Proof
	deriving (Eq, Show)

 data Side = LeftSide | RightSide
	deriving (Eq, Show)

 shift :: Proof -> Proof -> Proof
 shift _ AXM = AXM
 shift u (EQU x y) = EQU (shift u x) (shift u y)
 shift _ (SMB s) = SMB s
 shift _ DB0 = DB0
 shift u (DBS x) = if u == DBS x then DBS u else DBS (shift u x)
 shift u (DBL x) = DBL (shift (DBS u) x)
 shift u (APL x y) = APL (shift u x) (shift u y)
 shift u (LTR x y) = LTR (shift u x) (shift u y)
 shift u (LTS x y) = LTS (shift u x) (shift u y)
 shift u (SUB x y) = SUB (shift u x) (shift u y)
 shift u (RED x) = RED (shift u x)
 shift u (LFT x) = LFT (shift u x)
 shift u (RGT x) = RGT (shift u x)
 shift u (RFL x) = RFL (shift u x)

 subst :: Proof -> Proof -> Proof -> Proof
 subst1 :: Proof -> Proof -> Proof -> Proof
 subst u a b = if u == a then b else (if DBS u == a then u else subst1 u a b)
 subst1 _ AXM b = AXM
 subst1 u (EQU x y) b = EQU (subst u x b) (subst u y b)
 subst1 _ (SMB s) _ = SMB s
 subst1 _ DB0 _ = DB0
 subst1 u (DBS x) b = DBS (subst u x b)
 subst1 u (DBL x) b = DBL (subst (DBS u) x (shift DB0 b))
 subst1 u (APL x y) b = APL (subst u x b) (subst u y b)
 subst1 u (LTR x y) b = LTR (subst u x b) (subst u y b)
 subst1 u (LTS x y) b = LTS (subst u x b) (subst u y b)
 subst1 u (SUB x y) b = SUB (subst u x b) (subst u y b)
 subst1 u (RED x) b = RED (subst u x b)
 subst1 u (LFT x) b = LFT (subst u x b)
 subst1 u (RGT x) b = RGT (subst u x b)
 subst1 u (RFL x) b = RFL (subst u x b)

 cont :: Proof -> Proof -> Bool
 cont1 :: Proof -> Proof -> Bool
 cont x y = if x == y then True else cont1 x y
 cont1 AXM _ = False
 cont1 (EQU x y) z = (cont x z) || (cont y z)
 cont1 (SMB _) _ = False
 cont1 DB0 _ = False
 cont1 (DBS x) y = cont x y
 cont1 (DBL x) y = cont x y
 cont1 (APL x y) z = (cont x z) || (cont y z)
 cont1 (LTR x y) z = (cont x z) || (cont y z)
 cont1 (LTS x y) z = (cont x z) || (cont y z)
 cont1 (SUB x y) z = (cont x z) || (cont y z)
 cont1 (RED x) y = cont x y
 cont1 (LFT x) y = cont x y
 cont1 (RGT x) y = cont x y
 cont1 (RFL x) y = cont x y

 red1 :: Proof -> Proof
 red1 AXM = AXM
 red1 (EQU x y) = EQU (red1 x) (red1 y)
 red1 (SMB s) = SMB s
 red1 DB0 = DB0
 red1 (DBS x) = DBS (red1 x)
 red1 (DBL x) = DBL (red1 x)
 red1 (APL (DBL x) y) = subst DB0 x y
 red1 (APL x y) = APL (red1 x) (red1 y)
 red1 (LTR x y) = LTR (red1 x) (red1 y)
 red1 (LTS x y) = LTS (red1 x) (red1 y)
 red1 (SUB x y) = SUB (red1 x) (red1 y)
 red1 (RED x) = RED (red1 x)
 red1 (LFT x) = LFT (red1 x)
 red1 (RGT x) = RGT (red1 x)
 red1 (RFL x) = RFL (red1 x)

 red2 :: [Proof] -> [Proof]
 red2 [] = []
 red2 (x : l) = (red1 x) : (x : l)

 red3 :: [Proof] -> [Proof]
 red3 [] = []
 -- red3 (x : l) = if elem x l then (x : l) else red3 (red2 (x : l))
 red3 (x : l) = case find (\y -> cont x y) l of
	Nothing -> red3 (red2 (x : l))
	Just _ -> x : l

 red :: Proof -> Proof
 red x = case red3 (x : []) of
		[] -> x
		y : m -> y
 -- red x = if red1 x == x then x else red (red1 x)

 side :: Side -> Proof -> Proof -> Proof -> Proof
 side LeftSide a b AXM = a
 side RightSide a b AXM = b
 side LeftSide _ _ (EQU x y) = x
 side RightSide _ _ (EQU x y) = y
 side _ _ _ (SMB s) = SMB s
 side _ _ _ DB0 = DB0
 side s a b (DBS x) = DBS (side s a b x)
 side s a b (DBL x) = DBL (side s a b x)
 side s a b (APL x y) = APL (side s a b x) (side s a b y)
 side s a b (LTR x y) = 
	let lx = side LeftSide a b x
	    ly = side LeftSide a b y
	in let rlx = red lx
	       rly = red ly
	   in if (lx == ly) || (lx == rly) || (rlx == ly) || (rlx == rly) 
	      -- then red (side RightSide a b (if s == LeftSide then x else y))
          then (if s == LeftSide then (side RightSide a b x) else red (side RightSide a b y))
	      else LTR x y
 -- if red (side LeftSide a b x) == red (side LeftSide a b y) then (side RightSide a b (if s == LeftSide then x else y)) else LTR x y
 side s a b (LTS x y) = if (side LeftSide a b x) == (side LeftSide a b y) then (side RightSide a b (if s == LeftSide then x else y)) else LTR x y
 -- side LeftSide a b (SUB x y) = APL (DBL x) y
 -- side RightSide a b (SUB x y) = subst DB0 x y
 side LeftSide a b (SUB x y) = APL (DBL (side LeftSide a b x)) (side LeftSide a b y)
 side RightSide a b (SUB x y) = subst DB0 (side RightSide a b x) (side RightSide a b y)
 side LeftSide a b (RED x) = side LeftSide a b x
 side RightSide a b (RED x) = red (side RightSide a b x)
 side _ a b (LFT x) = side LeftSide a b x
 side _ a b (RGT x) = side RightSide a b x
 side _ _ _ (RFL x) = x   

 var :: String -> Proof
 var x = SMB x

 contSmb :: Proof -> String -> Bool
 contSmb AXM _ = False
 contSmb (EQU x y) s = (contSmb x s) || (contSmb y s)
 contSmb (SMB s1) s2 = s1 == s2
 contSmb DB0 _ = False
 contSmb (DBS x) s = contSmb x s
 contSmb (DBL x) s = contSmb x s
 contSmb (APL x y) s = (contSmb x s) || (contSmb y s)
 contSmb (LTR x y) s = (contSmb x s) || (contSmb y s)
 contSmb (LTS x y) s = (contSmb x s) || (contSmb y s)
 contSmb (SUB x y) s = (contSmb x s) || (contSmb y s)
 contSmb (RED x) s = contSmb x s
 contSmb (LFT x) s = contSmb x s
 contSmb (RGT x) s = contSmb x s
 contSmb (RFL x) s = contSmb x s

 abstr :: Proof -> String -> Proof -> Proof
 abstr1 :: Proof -> String -> Proof -> Proof
 abstr d v x = if (contSmb x v) then (abstr1 d v x) else x
 abstr1 _ _ AXM = AXM
 abstr1 d v (EQU x y) = EQU (abstr d v x) (abstr d v y)
 abstr1 d v (SMB s) = if v == s then d else (SMB s)
 abstr1 _ _ DB0 = DB0
 abstr1 d v (DBS x) = DBS (abstr d v x)
 abstr1 d v (DBL x) = DBL (abstr (DBS d) v x)
 abstr1 d v (APL x y) = APL (abstr d v x) (abstr d v y)
 abstr1 d v (LTR x y) = LTR (abstr d v x) (abstr d v y)
 abstr1 d v (LTS x y) = LTS (abstr d v x) (abstr d v y)
 abstr1 d v (SUB x y) = SUB (abstr d v x) (abstr d v y)
 abstr1 d v (RED x) = RED (abstr d v x)
 abstr1 d v (LFT x) = LFT (abstr d v x)
 abstr1 d v (RGT x) = RGT (abstr d v x)
 abstr1 d v (RFL x) = RFL (abstr d v x)
 
 lambda :: String -> Proof -> Proof
 lambda v x = DBL (abstr DB0 v x)

 apl2 :: Proof -> Proof -> Proof -> Proof
 apl2 f x1 x2 = APL (APL f x1) x2

 apl3 :: Proof -> Proof -> Proof -> Proof -> Proof
 apl3 f x1 x2 x3 = APL (APL (APL f x1) x2) x3

 axl = SMB "SMB"
 axr = APL (SMB "SMB") (SMB "SMB")

 left = side LeftSide axl axr
 right = side RightSide axl axr

 proves x = do
  putStr ("\nThe proof\n  " ++ show x ++ " \nproves\n  " ++ show (left x) ++ "\n= " ++ show (right x) ++ "\n")

 reducesTo x = do
  putStr ("\n  " ++ show x ++ "\nreduces to\n  " ++ show (red x) ++ "\n")

 ident = DBL DB0
 auto = DBL (APL DB0 DB0)
 comp f g = DBL (APL f (APL g DB0))
 fix f = APL auto (comp f auto)
 ias = fix (DBL (APL (SMB "SMB") DB0))

 parent = SMB "parent"
 gdparent = SMB "gdparent"
 allan = SMB "Allan"
 brenda = SMB "Brenda"
 charles = SMB "Charles"

 gpRule1 = lambda "x" $ lambda "y" $ lambda "z" $ 
  EQU (APL (apl2 parent (var "x") (var "y")) $
       APL (apl2 parent (var "y") (var "z")) $
       apl2 gdparent (var "x") (var "z"))
      ident
 gpAxiom1 = EQU (apl2 parent allan brenda) ident
 gpAxiom2 = EQU (apl2 parent brenda charles) ident

 gpLemma1c = apl3 gpRule1 allan brenda charles
 gpLemma2c = APL gpAxiom1 $ APL (apl2 parent brenda charles) $ apl2 gdparent allan charles
 gpLemma3c = LTR gpLemma2c gpLemma1c
 gpLemma4c = APL gpAxiom2 $ apl2 gdparent allan charles
 gpTheorem1c = LTR gpLemma4c gpLemma3c

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

 test = do
  proves (LTR (LTR AXM (SMB "SMB")) (APL (SMB "SMB") AXM))
  proves (LTR (LTR AXM (SMB "SMB")) (APL AXM (SMB "SMB")))
  proves (LTR (LTR AXM (SMB "SMB")) (APL AXM AXM))
  reducesTo (APL (APL (DBL DB0) (DBL DB0)) (APL (DBL DB0) (SMB "SMB")))
  reducesTo (fix ident)
  reducesTo (fix (DBL (APL (SMB "SMB") DB0)))  
  proves gpTheorem1c
  proves propTheorem1

