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

 left :: Proof -> Proof
 -- K = K
 left CombinatorK = CombinatorK
 -- S = S
 left CombinatorS = CombinatorS
 -- If x = y and z = w then x z = y w
 left (ApplyProof p q) = ApplyProof (left p) (left q)
 -- K x y = x
 left (AxiomK p q) = ApplyProof (ApplyProof CombinatorK (left p)) (left q)
 -- S x y z = x z (y z)
 left (AxiomS p q r) = ApplyProof (ApplyProof (ApplyProof CombinatorS (left p)) (left q)) (left r)
 -- If x = y and x = z then y = z
 left (Trans p q) = if left p == left q then right p else CombinatorK

 right :: Proof -> Proof
 -- K = K
 right CombinatorK = CombinatorK
 -- S = S
 right CombinatorS = CombinatorS
 -- If x = y and z = w then x z = y w
 right (ApplyProof p q) = ApplyProof (right p) (right q)
 -- K x y = x
 right (AxiomK p q) = right p
 -- S x y z = x z (y z)
 right (AxiomS p q r) = ApplyProof (ApplyProof (right p) (right r)) (ApplyProof (right q) (right r))
 -- If x = y and x = z then y = z
 right (Trans p q) = if left p == left q then right q else CombinatorK

 proves pr = do
  putStr ("\nThe proof\n  " ++ show pr ++ " \nproves\n  " ++ show (left pr) ++ "\n= " ++ show (right pr) ++ "\n")

 proof1 = Trans (Trans (AxiomS CombinatorK CombinatorK CombinatorK)
                       (Trans (AxiomK (ApplyProof (ApplyProof (ApplyProof CombinatorS CombinatorK) CombinatorK) CombinatorK) CombinatorK) 
                              (AxiomK (ApplyProof (ApplyProof (ApplyProof CombinatorS CombinatorK) CombinatorK) CombinatorK) CombinatorK)))
				(AxiomK CombinatorK (ApplyProof CombinatorK CombinatorK))

 test = do
  proves proof1

