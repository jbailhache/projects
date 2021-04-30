module CPL where
 
 import Data.List

 data Proof = Apply Proof Proof
            | Trans Proof Proof
            | K
            | S
            | Klaw Proof Proof
            | Slaw Proof Proof Proof
	deriving (Eq, Show)
	
 data Side = LeftSide | RightSide
	deriving (Eq, Show)

 side :: Side -> Proof -> Proof
 side s (Apply x y) = Apply (side s x) (side s y)
 side s (Trans x y) = if side LeftSide x == side LeftSide y then (if s == LeftSide then side RightSide x else side RightSide y)
                    else if (side RightSide x == side LeftSide y) then (if s == LeftSide then side LeftSide x else side RightSide y)
                    else if (side LeftSide x == side RightSide y) then (if s == LeftSide then side RightSide x else side LeftSide y)
                    else if (side RightSide x == side RightSide y) then (if s == LeftSide then side LeftSide x else side RightSide y)
                    else Trans x y
 side s K = K
 side s S = S
 side LeftSide (Klaw x y) = Apply (Apply K (side LeftSide x)) (side LeftSide y)
 side RightSide (Klaw x y) = side RightSide x
 side LeftSide (Slaw x y z) = Apply (Apply (Apply S (side LeftSide x)) (side LeftSide y)) (side LeftSide z)
 side RightSide (Slaw x y z) = Apply (Apply (side RightSide x) (side RightSide z)) (Apply (side RightSide y) (side RightSide z))

 left = side LeftSide 
 right = side RightSide 

 proves x = do
  putStr ("\nThe proof\n  " ++ show x ++ " \nproves\n  " ++ show (left x) ++ "\n= " ++ show (right x) ++ "\n")

 test = do
  proves (Trans (Slaw K K K) (Klaw K (Apply K K)))

