--#include "naturals.agda"
open Naturals use Nat, Seq
--#include "amenities.agda"
open Amenities use N1, star, arr

limitStructure (D :: Set) :: Set
  = sig zero :: D 
        succ :: D -> D
        limit :: Seq D -> D

limitFunctor (D :: Set) :: Set
  = data zero 
       | succ (p :: D) 
       | limit (fs :: Seq D)

limitFunctorMap 
      (D1, D2 :: Set) 
      ( f :: arr D1 D2) 
  :: arr (limitFunctor D1) (limitFunctor D2)
  = \(a::limitFunctor D1) -> 
     case a of 
        (zero) -> zero@_
        (succ p) -> succ@_ (f p)
        (limit fs) -> limit@_ (\(n::Nat) -> f (fs n))

Ot :: Set 
  = data mu (x :: limitFunctor Ot)

Ot_ls :: limitStructure Ot 
  = struct 
      zero = mu@_ zero@_ 
      succ = \(h::Ot) -> mu@_ (succ@_ h)
      limit = \(h::Seq Ot) -> mu@_ (limit@_ h)

B (P :: Ot -> Set) (a :: Ot) :: Set
  = case a of 
     (mu x) -> case x of 
                 (zero) -> N1
                 (succ p) -> P p
                 (limit fs) -> (n::Nat) -> P (fs n)

--#include "subset.agda"
open predicates Ot 
  use Pred, Subset, Monotone, PreFP

{- Lemma that B is monotone -}

BM :: Monotone B 
  = \(P, Q :: Pred) -> 
    \(h :: P `Subset` Q) ->
    \(i :: Ot) -> 
    \(h' :: B P i) -> 
    case i of 
     (mu x) -> 
       case x of
          (zero) -> star
          (succ p) -> h p h'
          (limit fs) -> \(n::Nat) -> h (fs n) (h' n)

{- A progressive predicate is a pre-fixedpoint of B -}

Progressive (P :: Pred) :: Set
  = P `PreFP` B 

{- a is in the intersection of all progressive
   predicates. -}

WF (a :: Ot) :: Type
  = (P :: Pred)-> 
Progressive P -> P a
