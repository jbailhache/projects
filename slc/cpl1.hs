module CPL where
 
 import Data.List

 data Proof = APL Proof Proof
            | GTR Proof Proof
            | K
            | S
            | KL
            | SL
	deriving (Eq, Show)
	
 data Side = LeftSide | RightSide
	deriving (Eq, Show)

 side :: Side -> Proof -> Proof
 side s (APL x y) = APL (side s x) (side s y)
 side s (LTR x y) = if red (side LeftSide x) == red (side LeftSide y) then (side RightSide (if s == LeftSide then x else y)) else LTR x y

 left = side LeftSide 
 right = side RightSide 

 proves x = do
  putStr ("\nThe proof\n  " ++ show x ++ " \nproves\n  " ++ show (left x) ++ "\n= " ++ show (right x) ++ "\n")

