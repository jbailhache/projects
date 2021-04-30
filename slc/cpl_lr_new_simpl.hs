module CL where

 data Proof =
    K
  | S
  | Apply Proof Proof
  | AxiomK Proof Proof
  | AxiomS Proof Proof Proof
  | Trans Proof Proof
  deriving (Eq, Show)

 left :: Proof -> Proof
 -- K = K
 left K = K
 -- S = S
 left S = S
 -- If x = y and z = w then x z = y w
 left (Apply p q) = Apply (left p) (left q)
 -- K x y = x
 left (AxiomK p q) = Apply (Apply K (left p)) (left q)
 -- S x y z = x z (y z)
 left (AxiomS p q r) = Apply (Apply (Apply S (left p)) (left q)) (left r)
 -- If x = y and x = z then y = z
 left (Trans p q) = if left p == left q then right p else K

 right :: Proof -> Proof
 -- K = K
 right K = K
 -- S = S
 right S = S
 -- If x = y and z = w then x z = y w
 right (Apply p q) = Apply (right p) (right q)
 -- K x y = x
 right (AxiomK p q) = right p
 -- S x y z = x z (y z)
 right (AxiomS p q r) = Apply (Apply (right p) (right r)) (Apply (right q) (right r))
 -- If x = y and x = z then y = z
 right (Trans p q) = if left p == left q then right q else K

 proves pr = do
  putStr ("\nThe proof\n  " ++ show pr ++ " \nproves\n  " ++ show (left pr) ++ "\n= " ++ show (right pr) ++ "\n")

 proof1 = Trans (Trans (AxiomS K K K)
                       (Trans (AxiomK (Apply (Apply (Apply S K) K) K) K) 
                              (AxiomK (Apply (Apply (Apply S K) K) K) K)))
				(AxiomK K (Apply K K))

 test = do
  proves proof1

