module Rhsz where

 data Expr
  = Zero
  | Suc
  | H
  | H1
  | R1
  | R2 
  | R3
  | Ap Expr Expr

 one = Ap Suc Zero
 omega = Ap (Ap H Suc) Zero

 instance Show Expr where
  show Zero = "0"
  show Suc = "suc"
  show H = "H"
  show H1 = "H1"
  show R1 = "R1"
  show R2 = "R2"
  show R3 = "R3"
  show (Ap x y) = "(" ++ show x ++ " " ++ show y ++ ")"



