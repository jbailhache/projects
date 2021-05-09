module CL where

 data Combination = Variable String | I | K | B | C | S | Apply Combination Combination
  deriving (Eq, Show)
 
 contains :: Combination -> Combination -> Bool
 contains1 :: Combination -> Combination -> Bool
 contains x y = if x == y then True else contains1 x y
 contains1 (Variable _) _ = False
 contains1 I _ = False
 contains1 K _ = False
 contains1 B _ = False
 contains1 C _ = False
 contains1 S _ = False
 contains1 (Apply x y) z = contains x z || contains y z
 
 abstract :: Combination -> Combination -> Combination
 abstract x y = case y of
  Variable v -> if x == y then I else Apply K y
  I -> Apply K y
  K -> Apply K y
  B -> Apply K y
  C -> Apply K y
  S -> Apply K y
  Apply m n -> 
   if n == x && not (contains m x) then m
   else if not (contains y x) then Apply K y
   else if not (contains m x) then Apply (Apply B m) (abstract x n)
   else if not (contains n x)  then Apply (Apply C (abstract x m)) n
   else Apply (Apply S (abstract x m)) (abstract x n)
 