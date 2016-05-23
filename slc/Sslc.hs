module Sslc where
 
 import Data.List

 data Proof = AXM
            | SMB 
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
 shift _ SMB = SMB
 shift _ DB0 = DB0
 shift u (DBS x) = if u == DBS x then DBS u else DBS (shift u x)
 shift u (DBL x) = DBL (shift (DBS u) x)
 shift u (APL x y) = APL (shift u x) (shift u y)
 shift u (LTR x y) = LTR (shift u x) (shift u y)

 subst :: Proof -> Proof -> Proof -> Proof
 subst1 :: Proof -> Proof -> Proof -> Proof
 subst u a b = if u == a then b else (if DBS u == a then u else subst1 u a b)
 subst1 _ AXM b = AXM
 subst1 _ SMB _ = SMB
 subst1 _ DB0 _ = DB0
 subst1 u (DBS x) b = DBS (subst u x b)
 subst1 u (DBL x) b = DBL (subst (DBS u) x (shift DB0 b))
 subst1 u (APL x y) b = APL (subst u x b) (subst u y b)
 subst1 u (LTR x y) b = LTR (subst u x b) (subst u y b)

 cont :: Proof -> Proof -> Bool
 cont1 :: Proof -> Proof -> Bool
 cont x y = if x == y then True else cont1 x y
 cont1 AXM _ = False
 cont1 SMB _ = False
 cont1 DB0 _ = False
 cont1 (DBS x) y = cont x y
 cont1 (DBL x) y = cont x y
 cont1 (APL x y) z = (cont x z) || (cont y z)
 cont1 (LTR x y) z = (cont x z) || (cont y z)

 red1 :: Proof -> Proof
 red1 AXM = AXM
 red1 SMB = SMB
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
 side _ _ _ SMB = SMB
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

 axl = SMB
 axr = APL SMB SMB

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
 ias = fix (DBL (APL SMB DB0))

 test = do
  proves (LTR (LTR AXM SMB) (APL SMB AXM))
  proves (LTR (LTR AXM SMB) (APL AXM SMB))
  proves (LTR (LTR AXM SMB) (APL AXM AXM))
  reducesTo (APL (APL (DBL DB0) (DBL DB0)) (APL (DBL DB0) SMB))
  reducesTo (fix ident)
  reducesTo (fix (DBL (APL SMB DB0)))  

