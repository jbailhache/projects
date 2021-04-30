module CL where

 data Combinator = K | S | Apply Combinator Combinator
  deriving (Eq, Show)
  
 data Proof =
    CombinatorK
  | CombinatorS
  | ApplyProof Proof Proof
  | AxiomK Proof Proof
  | AxiomS Proof Proof Proof
  | Trans Proof Proof
  deriving (Eq, Show)
  
 data Equality = Equality Combinator Combinator
  deriving (Eq, Show)

 -- K = K
 conclusion CombinatorK = Equality K K
 -- S = S
 conclusion CombinatorS = Equality S S
 -- If x = y and z = w then x z = y w
 conclusion (ApplyProof p q) = 
  let Equality x y = conclusion p in
  let Equality z w = conclusion q in
  Equality (Apply x z) (Apply y w)
 -- K x y = y
 conclusion (AxiomK p q) = 
  let Equality x1 x2 = conclusion p in
  let Equality y1 y2 = conclusion q in
  Equality (Apply (Apply K x1) y1) x2
 -- S x y z = x z (y z)
 conclusion (AxiomS p q r) = 
  let Equality x1 x2 = conclusion p in
  let Equality y1 y2 = conclusion q in
  let Equality z1 z2 = conclusion r in
  Equality (Apply (Apply (Apply S x1) y1) z1) (Apply (Apply x2 z2) (Apply y2 z2))
 -- If x = y and x = z then y = z
 conclusion (Trans p q) = 
  let Equality x1 y = conclusion p in
  let Equality x2 z = conclusion q in
  if x1 == x2 then Equality y z else Equality K K
 -- If x = y then x z = y z

 proves pr = do
  putStr ("\nThe proof\n  " ++ show pr ++ " \nproves\n  " ++ show (conclusion pr) ++ "\n")

 proof1 = Trans (Trans (AxiomS CombinatorK CombinatorK CombinatorK)
                       (Trans (AxiomK (ApplyProof (ApplyProof (ApplyProof CombinatorS CombinatorK) CombinatorK) CombinatorK) CombinatorK) 
                              (AxiomK (ApplyProof (ApplyProof (ApplyProof CombinatorS CombinatorK) CombinatorK) CombinatorK) CombinatorK)))
				(AxiomK CombinatorK (ApplyProof CombinatorK CombinatorK))
					   
 test = do
  proves proof1
