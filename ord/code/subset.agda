{- predicates over a set, intersection -}

--#include "amenities.agda"
open Amenities use arr, and

package predicates (D :: Set) where 

  Pred :: Type = D -> Set
  Op   :: Set  = D -> D
  Op2  :: Set  = D -> Op 

  Subset (P, Q :: Pred) :: Set
   = (i :: D)-> P i -> Q i

  SubsetReflexive (P :: Pred) 
   :: P `Subset` P
   = \(i::D) -> \(h::P i) -> h

  SubsetTransitive 
    (P, Q, R :: Pred) 
    (h1 :: P `Subset` Q )
    (h2 :: Q `Subset` R )
   :: P `Subset` R
   = \(i::D) -> \(h::P i) -> 
     h2 i (h1 i h)

  Sub (P :: Pred) (f :: Op) :: Pred 
   = \(i :: D)  -> P (f i)

  {- monotonicity of pts. -}

  Monotone (F :: Pred -> Pred) :: Type
   = (P, Q :: Pred) -> 
     P `Subset` Q -> F P `Subset` F Q

  SubIsMonotone (f :: Op ) 
   :: Monotone (\(P :: Pred)-> P `Sub` f)
   = \(P,Q::Pred) -> \(h::Subset P Q) -> 
     \(i::D) -> 
     h (f i) 

  IdentityMonotone 
   :: Monotone (\(P :: Pred)-> P)
   = \(P,Q::Pred) -> \(h::Subset P Q) -> h

  {- Property of a predicate that it is closed
     under an operation. -}

  ClosedUnder (P :: Pred) (f :: Op) :: Set
   = P `Subset` (P `Sub` f) 

  {- The generalised Gentzen transform -}

  Gentzen (P :: Pred) (f :: Op2) :: Pred
   = \(h::D) -> P `ClosedUnder` (f h)

  {- general intersection -} 

  Cap (G :: Set) (Ps :: G -> Pred) :: Pred
   = \(i :: D) -> 
     (g :: G) -> Ps g i 

  CapOut (G :: Set)( Ps :: G -> Pred)
   :: (g :: G) -> Cap G Ps `Subset` Ps g  
   = \(g :: G)-> 
     \(i :: D) -> 
     \(h :: Cap G Ps i) -> 
     h g

  CapIn (G :: Set)( Ps :: G -> Pred)
        (Q :: Pred) 
        (h :: (g :: G)-> Q `Subset` Ps g )
   :: Q `Subset` Cap G Ps
   = \(i::D) -> 
     \(h'::Q i) -> 
     \(g::G) -> 
     h g i h'

  {- binary intersection -}

  Cap2 (P, Q :: Pred) :: Pred
   = \(i :: D)-> P i `and` Q i
  
  Cap2InL (P, Q :: Pred)
   :: (P `Cap2` Q) `Subset` P 
   = \(i::D) -> \(h::Cap2 P Q i) -> h.fst

  Cap2InR (P, Q :: Pred)
   :: (P `Cap2` Q) `Subset` Q 
   = \(i::D) -> \(h::Cap2 P Q i) -> h.snd

  Cap2Out( P, Q , R :: Pred ) 
         ( h1 :: R `Subset` P )
         ( h2 :: R `Subset` Q )
   :: R `Subset` (P `Cap2` Q)
   = \(i::D) -> 
     \(h::R i) -> 
     struct  fst = h1 i h
             snd = h2 i h

  PreFP (P :: Pred) ( F :: Pred -> Pred) 
   :: Set
   = F P `Subset` P

  {- If a predicate transformer is monotone, 
     then its algebras (ie. the predicates
     which are pre-fixed points of it, or are
     progressive with respect to it) are closed 
     under arbitrary intersection -}
  Lemma ( B :: Pred -> Pred )
        ( mB :: Monotone B )
        ( G :: Set )
        ( Ps :: G -> Pred ) 
        ( h :: (g :: G) -> PreFP (Ps g) B )
        :: PreFP (Cap G Ps) B 
   = {- we prove it by using CapIn, since that is how we get
        to prove that predicates are subsets of an intersection.

        So we have to prove that B (Cap G Ps) `Subset` Ps g 
        for each g. We prove this by transitivity. Since
        we have (Cap G Ps) `Subset` Ps g, and B is monotone, 
        we have B (Cap G Ps) `Subset` B (Ps g). But 
        B (Ps g) `Subset` Ps g, by hypothesis.
     -} 
     let { foo( g :: G) :: Subset (B (Cap G Ps)) (Ps g) 
            = SubsetTransitive (B (Cap G Ps)) 
                               (B (Ps g)) 
                               (Ps g) 
                        (mB (Cap G Ps) (Ps g) 
                            (CapOut G Ps g)) 
                        (h g)
     } in 
CapIn G Ps (B (Cap G Ps)) foo 
