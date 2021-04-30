module CPL where
 
 import Data.List

 data Proof = APL Proof Proof
            | GTR Proof Proof
            | K
            | S
            | KL Proof Proof
            | SL Proof Proof Proof
	deriving (Eq, Show)
	
 data Side = LeftSide | RightSide
	deriving (Eq, Show)

 side :: Side -> Proof -> Proof
 side s (APL x y) = APL (side s x) (side s y)
 side s (GTR x y) = if side LeftSide x == side LeftSide y then (if s == LeftSide then side RightSide x else side RightSide y)
                    else if (side RightSide x == side LeftSide y) then (if s == LeftSide then side LeftSide x else side RightSide y)
                    else if (side LeftSide x == side RightSide y) then (if s == LeftSide then side RightSide x else side LeftSide y)
                    else if (side RightSide x == side RightSide y) then (if s == LeftSide then side LeftSide x else side RightSide y)
                    else GTR x y
 side s K = K
 side s S = S
 side LeftSide (KL x y) = APL (APL K (side LeftSide x)) (side LeftSide y)
 side RightSide (KL x y) = side RightSide x
 side LeftSide (SL x y z) = APL (APL (APL S (side LeftSide x)) (side LeftSide y)) (side LeftSide z)
 side RightSide (SL x y z) = APL (APL (side RightSide x) (side RightSide z)) (APL (side RightSide y) (side RightSide z))

 left = side LeftSide 
 right = side RightSide 

 proves x = do
  putStr ("\nThe proof\n  " ++ show x ++ " \nproves\n  " ++ show (left x) ++ "\n= " ++ show (right x) ++ "\n")

 test = do
  proves (GTR (SL K K K) (KL K (APL K K)))

