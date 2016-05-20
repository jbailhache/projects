module Sslc where

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
 red3 (x : l) = if elem x l then (x : l) else red3 (red2 (x : l))

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
 side s a b (LTR x y) = if red (side LeftSide a b x) == red (side LeftSide a b y) then (side RightSide a b (if s == LeftSide then x else y)) else LTR x y

 axl = SMB
 axr = APL SMB SMB

 left = side LeftSide axl axr
 right = side RightSide axl axr

 proves x = do
  putStrLn ("The proof " ++ show x ++ " proves " ++ show (left x) ++ " = " ++ show (right x))

 reducesTo x = do
  putStrLn (show x ++ " reduces to " ++ show (red x))

 ident = DBL DB0
 auto = DBL (APL DB0 DB0)
 comp f g = DBL (APL f (APL g DB0))
 fix f = APL auto (comp f auto)

 test = do
  proves (LTR (LTR AXM SMB) (APL SMB AXM))
  proves (LTR (LTR AXM SMB) (APL AXM SMB))
  proves (LTR (LTR AXM SMB) (APL AXM AXM))
  reducesTo (APL (APL (DBL DB0) (DBL DB0)) (APL (DBL DB0) SMB))
  reducesTo (fix ident)
  



