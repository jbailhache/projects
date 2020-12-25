module Sslc where
 
 import Data.List

 data Proof = AXM
			| EQU Proof Proof
            | SMB String
            | DB0 
            | DBS Proof
            | DBL Proof
            | APL Proof Proof
            | LTR Proof Proof
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

 cont :: Proof -> Proof -> Bool
 cont1 :: Proof -> Proof -> Bool
 cont x y = if x == y then True else cont1 x y
 cont1 AXM _ = False
 cont1 (EQU x y) z = (cont x z) || (cont y z)
 cont1 (SMB s) _ = False
 cont1 DB0 _ = False
 cont1 (DBS x) y = cont x y
 cont1 (DBL x) y = cont x y
 cont1 (APL x y) z = (cont x z) || (cont y z)
 cont1 (LTR x y) z = (cont x z) || (cont y z)

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
	      then red (side RightSide a b (if s == LeftSide then x else y))
          -- then (if s == LeftSide then (side RightSide a b x) else red (side RightSide a b y))
	      else LTR x y
 -- if red (side LeftSide a b x) == red (side LeftSide a b y) then (side RightSide a b (if s == LeftSide then x else y)) else LTR x y


 contSmb :: Proof -> String -> Bool
 contSmb x s = cont x (SMB s)
 
 abstr :: Proof -> String -> Proof -> Proof
 abstr1 :: Proof -> String -> Proof -> Proof
 abstr d v x = if (contSmb x v) then (abstr1 d v x) else x
 abstr1 d v AXM = AXM
 abstr1 d v (EQU x y) = EQU (abstr d v x) (abstr d v y)
 abstr1 d v (SMB s) = if v == s then d else (SMB s)
 abstr1 d v DB0 = DB0
 abstr1 d v (DBS x) = DBS (abstr d v x)
 abstr1 d v (DBL x) = DBL (abstr (DBS d) v x)
 abstr1 d v (APL x y) = APL (abstr d v x) (abstr d v y)
 abstr1 d v (LTR x y) = LTR (abstr d v x) (abstr d v y)
 
 lambda :: String -> Proof -> Proof
 lambda v x = DBL (abstr DB0 v x)

 
 axl = SMB "a"
 axr = APL (SMB "a") (SMB "a")

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
 ias = fix (DBL (APL (SMB "a") DB0))

 apl2 f x y = APL (APL f x) y
 apl3 f x y z = APL (APL (APL f x) y) z

 parent = SMB "parent"
 gdparent = SMB "gdparent"
 allan = SMB "allan"
 brenda = SMB "brenda"
 charles = SMB "charles"

 gpRule1 = lambda "x" $ lambda "y" $ lambda "z" $ 
  EQU (APL (apl2 parent (SMB "x") (SMB "y")) $
       APL (apl2 parent (SMB "y") (SMB "z")) $
       apl2 gdparent (SMB "x") (SMB "z"))
      ident
 gpAxiom1 = EQU (apl2 parent allan brenda) ident
 gpAxiom2 = EQU (apl2 parent brenda charles) ident
 
 gpLemma1c = apl3 gpRule1 allan brenda charles
 gpLemma2c = APL gpAxiom1 $ APL (apl2 parent brenda charles) $ apl2 gdparent allan charles
 gpLemma3c = LTR gpLemma2c gpLemma1c
 gpLemma4c = APL gpAxiom2 $ apl2 gdparent allan charles
 gpTheorem1c = LTR gpLemma4c gpLemma3c
 
 
 test = do
  proves (LTR (LTR AXM (SMB "a")) (APL (SMB "a") AXM))
  proves (LTR (LTR AXM (SMB "a")) (APL AXM (SMB "a")))
  proves (LTR (LTR AXM (SMB "a")) (APL AXM AXM))
  reducesTo (APL (APL (DBL DB0) (DBL DB0)) (APL (DBL DB0) (SMB "a")))
  reducesTo (fix ident)
  reducesTo (fix (DBL (APL (SMB "a") DB0)))  

