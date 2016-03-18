--#include "amenities.agda"
--#include "naturals.agda"

{- This package assembles together things that
   are connected with the Gentzen lens, for
   the datatype of formal ordinals -}

package Ordinals where

  open Amenities use 
     Pi, implies , and, 
     N1, N0

  open Naturals use 
     Nat, It, Rec, Seq

  Ord :: Set = data O 
                  | S (a :: Ord) 
                  | L (ls :: (n :: Nat)->Ord)

  {- Some less barbarous notation -}  
  zero  :: Ord        = O@Ord
  succ  :: Ord -> Ord = S@Ord
  limit :: (Nat -> Ord) -> Ord = L@Ord

  {------ The transition structure on Ord ---}

  {- Cofinality -}
  C (a :: Ord) :: Set
    = case a of 
        (O)    -> N0
        (S a') -> N1
        (L ls) -> Nat
  
  {- Predecessor -}
  pd (a :: Ord) (t :: C a) :: Ord
    = case a of 
        (O)    -> case t of { }
        (S a') -> a'
        (L ls) -> ls t

  {--------- operations from Ords to Ords ------------}
  
  Op :: Set = Ord -> Ord 

  {- Composing operations -}  
  Comp :: Op -> Op -> Op
     = \(f :: Op) -> \(g :: Op) -> \(a :: Ord) -> 
       f (g a)

  {- Iterating operations, to get a sequence -}
  OpIt :: Op -> Seq Op
     = It Ord 

  {- pointwise limit of a seuence of operations -}
  OpLim :: Seq Op -> Op
     = \(fs :: Nat -> Op) -> \(a :: Ord) -> 
       limit (\(n :: Nat) -> fs n a)  

  {- omega iterating an operation -}
  OpItw :: Op -> Op
     = \(f :: Op) -> OpLim (OpIt f)

  {------------ Cantor hierarchy -------------------}

  {- recursive (in second argument). -}
  w :: Ord -> Ord -> Ord
     = \(a :: Ord) -> 
       \(b :: Ord) -> 
        case b of 
          (O)    -> succ a
          (S b') -> OpItw (\(x :: Ord) -> x `w` b') a
          (L ls) -> limit (\(n :: Nat) -> a `w` (ls n))

  {- The function a |-> w^a -}
  wexp :: Op = w zero

  {-------- Things related to the Veblen hierarchy --------}

  {- \a -> (f.(+1))^a (f 0) : an essential part of derivative -} 
  {- recursive. -}
  Nabla :: Op -> Op
     = \(f :: Op) -> \(a :: Ord) -> 
       case a of 
         (O)    -> f zero
         (S a') -> f (succ (Nabla f a'))
         (L ls) -> limit (\(n :: Nat) -> Nabla f (ls n))

  {- derivative of a normal function -}
  deriv :: Op -> Op
     = \(f :: Op) -> Nabla (OpItw f) 

  {- derivative of a sequence of normal function -}
  derivl :: (Nat -> Op) -> Op
     = \(sf :: Nat -> Op) -> Nabla (OpLim sf) 

  {- Veblen hierarchy -}
  {- recursive -}
  v :: Ord -> Ord -> Ord
     = \(a :: Ord) -> 
        let { pds :: Seq Op = 
                 case a of 
                   (O)    -> OpIt (w a) 
                   (S a') -> OpIt (v a')
                   (L ls) -> \(n :: Nat) -> v (ls n)
        } in Nabla (OpLim pds)

  veb :: Op 
    = \(a :: Ord) -> v a zero

  {-------- The landmark ordinals ------------}

  epsilon0 :: Ord = veb zero

  Gamma0 :: Ord = limit (\ (n :: Nat) -> 
      It Ord veb n zero)
