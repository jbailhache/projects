module CL where

 data Combinator = K | S | Apply Combinator Combinator
  deriving (Eq, Show)
  
 data Proof =
    AxiomK Combinator Combinator
  | AxiomS Combinator Combinator Combinator
  | Trans Proof Proof
  | ApplyRight Proof Combinator
  | ApplyLeft Proof Combinator
  deriving (Eq, Show)

 left :: Proof -> Combinator
 -- K x y = y
 left (AxiomK x y) = Apply (Apply K x) y
 -- S x y z = x z (y z)
 left (AxiomS x y z) = Apply (Apply (Apply S x) y) z
 -- If x = y and x = z then y = z
 left (Trans p q) = if left p == left q then right p else K
 -- If x = y then x z = y z
 left (ApplyRight p z) = Apply (left p) z
 -- If x = y then z x = z y
 left (ApplyLeft p z) = Apply z (left p)

 right :: Proof -> Combinator
 -- K x y = y
 right (AxiomK x y) = x
 -- S x y z = x z (y z)
 right (AxiomS x y z) = Apply (Apply x z) (Apply y z)
 -- If x = y and x = z then y = z
 right (Trans p q) = if left p == left q then right q else K
 -- If x = y then x z = y z
 right (ApplyRight p z) = Apply (right p) z
 -- If x = y then z x = z y
 right (ApplyLeft p z) = Apply z (right p)

 proves pr = do
  putStr ("\nThe proof\n  " ++ show pr ++ " \nproves\n  " ++ show (left pr) ++ "\n= " ++ show (right pr) ++ "\n")

 proof1 = Trans (Trans (AxiomS K K K)
                       (Trans (AxiomK (Apply (Apply (Apply S K) K) K) K) 
                              (AxiomK (Apply (Apply (Apply S K) K) K) K)))
				(AxiomK K (Apply K K))
 test = do
  proves proof1

