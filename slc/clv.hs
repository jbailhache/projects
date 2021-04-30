module CL where

 data Combination = K | S | Apply Combination Combination | Variable String
  deriving (Eq, Show)
  
 data Proof =
    AxiomK Combination Combination
  | AxiomS Combination Combination Combination
  | Trans Proof Proof
  | ApplyRight Proof Combination
  | ApplyLeft Proof Combination
  deriving (Eq, Show)
  
 data Equality = Equality Combination Combination
  deriving (Eq, Show)
  
 -- K x y = x
 conclusion (AxiomK x y) = Equality (Apply (Apply K x) y) x

 -- S x y z = x z (y z)
 conclusion (AxiomS x y z) = Equality (Apply (Apply (Apply S x) y) z) (Apply (Apply x z) (Apply y z))

 -- If x = y and x = z then y = z
 conclusion (Trans p q) = 
  let Equality x1 y = conclusion p in
  let Equality x2 z = conclusion q in
  if x1 == x2 then Equality y z else Equality K K

 -- If x = y then x z = y z
 conclusion (ApplyRight p z) = 
  let Equality x y = conclusion p in
  Equality (Apply x z) (Apply y z)

 -- If x = y then z x = z y
 conclusion (ApplyLeft p z) = 
  let Equality x y = conclusion p in
  Equality (Apply z x) (Apply z y)

 proves pr = do
  putStr ("\nThe proof\n  " ++ show pr ++ " \nproves\n  " ++ show (conclusion pr) ++ "\n")

 proof1 = Trans (Trans (AxiomS K K K)
                       (Trans (AxiomK (Apply (Apply (Apply S K) K) K) K) 
                              (AxiomK (Apply (Apply (Apply S K) K) K) K)))
                (AxiomK K (Apply K K))
					   
 test = do
  proves proof1
