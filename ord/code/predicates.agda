--#include "amenities.agda"
open Amenities use Pi, implies, Fam
--#include "naturals.agda"
open Naturals use Nat, Seq

{- Theory of "genuine" set-valued predicates over
  an arbitrary set D 
-}
package PredicatesX (D :: Set) where

  Pred :: Type
    = D -> Set

  {- A predicate transformer -}
  PredT :: Type
    = Pred -> Pred

  {---- assorted terminology --------}

  contains (P :: Pred) (a :: D) :: Set
    = P a  

  eps (a :: D) (P :: Pred) :: Set
    = contains P a

  {- that a predicate contains each of a sequence of Ds -}
  encloses (P :: Pred) (ls :: Seq D) :: Set
    = Pi Nat (\(n :: Nat)-> P `contains` ls n)

  {- that P is a subset of Q -}
  subset (P :: Pred) (Q :: Pred) :: Set
    = Pi D (\(a :: D) -> 
         P `contains` a `implies` (Q `contains` a))

  {- that this is transitive -}
  subsetTrans (P :: Pred) (Q :: Pred) (R :: Pred) 
    :: P `subset` Q -> Q `subset` R -> P `subset` R
    = \(h :: subset P Q) -> \(h' :: subset Q R) -> 
      \(a :: D) -> \(a' :: contains P a) -> h' a (h a a') 

  {- property of a PredT that it is monotone -}
  monotone ( F :: PredT ) :: Type
    = (P,Q :: Pred) -> 
        P `subset` Q -> F P `subset` F Q

  {- closed under a unary function -}
  closedUnder(P :: Pred) (f :: D -> D) :: Set
    = Pi D (\(a :: D) -> 
        (P `contains` a) `implies` (P `contains` (f a)))

  {- Generalised Gentzen transform -}
  Gentzen (f :: D -> D -> D) :: PredT
    = \(X::Pred) -> \(i::D) -> closedUnder X (f i)

  {- The following is really a theory of greatest
     lower bounds or infima; here specialised to
     the large partial order of predicates over a set.
  -}
  package Intersections (N :: Set) 
      (Ps :: N -> Pred) where 

    Cap :: Pred
      = \(a :: D) -> 
        (n :: N) -> Ps n a
  
    {- That Cap is a lower bound -} 

    CapOut 
      :: (n :: N) -> Cap `subset` (Ps n)
      = \(n :: N) -> 
        \(a :: D) -> 
        \(h' :: Cap `contains` a) -> 
        h' n
  
    {- That all lower bounds are subsets of Cap -} 

    CapIn (Q :: Pred)  
          (h :: (n :: N) -> Q `subset` Ps n )  
          :: Q `subset` Cap 
      = \(a :: D) -> 
        \(qa :: Q `contains` a) -> 
        \(n :: N) ->
        h n a qa

  {- The following package is relative to a predicate
     transformer, which we assume to be monotone. 
  -}
  package Progressive (B :: PredT)
       (mB :: monotone B ) where
     
    {- Progressivity -}
    Prog (P :: Pred ) :: Set
      = B P `subset` P 

    {- That progressive predicates are closed
       under intersections -}

    CapG (I :: Set) (Ps :: I -> Pred) :: Pred
      = (Intersections I Ps).Cap

    Lemma (I :: Set) (Ps :: I -> Pred) 
         (h :: (i :: I)-> Prog (Ps i))
         :: Prog (CapG I Ps)
      = open Intersections I Ps 
               use Cap, CapIn, CapOut
        in {- The proof is by CapIn, which our way of showing
              that something is a subset of Cap -}
           let {- What then remains to be proved -}
               rtp (i :: I) :: B Cap `subset` Ps i
                = let step1 
                        :: B Cap `subset` (B (Ps i))
                        = mB Cap (Ps i) (CapOut i)
                      qed 
                        :: B Cap `subset` Ps i
                        = subsetTrans (B Cap) (B (Ps i)) (Ps i) 
                                      step1 (h i) 
                  in  qed
           in CapIn (B Cap) rtp

    {- Preservation of progressivity -}
    PProg( F :: PredT ) :: Type
      = ( P :: Pred )-> Prog P -> Prog (F P)

   {- Let's try to understand when the Gentzen transform
      preserves progressivity -}

    Trial( f :: D -> D -> D) :: PProg( Gentzen f )
      = \(P::Pred) -> 
        \(h::Prog P) -> 
        \(a::D) -> 
        \(a':: Gentzen f P `B` a) -> 
        \(a0::D) -> 
        \(pa0::P `contains` a0) -> 
        h (f a a0) 
        {- :: P `B` f a a0 -}
        {! !}



