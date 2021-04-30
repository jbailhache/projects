module CL where

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
 left :: Proof -> Proof
 right :: Proof -> Proof
 left = side LeftSide 
 right = side RightSide
 -- a = b, c = d |- a c = b d
 side s (Apply x y) = Apply (side s x) (side s y)
 -- Generalized transitivity
 side s (Trans x y) = if left x == left y then (if s == LeftSide then right x else right y)
                      else if right x == left y then (if s == LeftSide then left x else right y)
                      else if left x == right y then (if s == LeftSide then right x else left y)
                      else if right x == right y then (if s == LeftSide then left x else right y)
                      else Trans x y
 -- K = K
 side _ K = K
 -- S = S
 side _ S = S
 -- a = a', b = b' |- K a b = a'
 side LeftSide (Klaw x y) = Apply (Apply K (left x)) (left y)
 side RightSide (Klaw x y) = right x
 -- a = a', b = b', c = c' |- S a b c = a' c' (b' c')
 side LeftSide (Slaw x y z) = Apply (Apply (Apply S (left x)) (left y)) (left z)
 side RightSide (Slaw x y z) = Apply (Apply (right x) (right z)) (Apply (right y) (right z))

 proves x = do
  putStr ("\nThe proof\n  " ++ show x ++ " \nproves\n  " ++ show (left x) ++ "\n= " ++ show (right x) ++ "\n")

 test = do
  proves (Trans (Slaw K K K) (Klaw K (Apply K K)))

