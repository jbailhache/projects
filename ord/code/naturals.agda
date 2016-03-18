package Naturals where

  {- the datatype -}

  Nat :: Set = data Z | S (p :: Nat)
  zero  :: Nat = Z@_
  succ (p :: Nat) :: Nat = S@_ p

  {- A convenient abbreviation. Note, we
     cannot use it to speak of sequences of Types. -}
  Seq (A :: Set) :: Set = Nat -> A
  
  {- recursion on Nat -}
  Rec (X :: Nat -> Set) 
         (x :: X zero) 
         (f :: (n :: Nat) -> X n -> X (succ n))  
         (n :: Nat) 
         :: X n
    = case n of 
         (Z)   -> x
         (S p) -> f p (Rec X x f p)
  
  {- iteration on Nat: f^n -}
  It (X :: Set) (f :: X -> X) (n :: Nat) 
      :: X -> X
    = \(x::X)-> Rec (\(_::Nat)->X) x (\(_::Nat)->f) n

  {- tail recursive version -}
  ItT (X :: Set) (f :: X -> X) (n :: Nat) :: X -> X
    = It (X -> X) 
         (\(g :: X -> X) -> \(x::X) -> g (f x))
         n
         (\(x :: X) -> x) 
