--#include "amenities.agda"
open Amenities use Pi, arr, Si

Fam (A :: Type) :: Type
  = sig  I :: Set
         f :: I -> A

package FamP (FS :: Fam Set) where

  U :: Set = FS.I
  T :: U -> Set = FS.f 

  {- "standard" next universe after U, T -}
  mutual 

    U' :: Set = data u 
                   | t (a :: U) 
                   | pi (a :: U') (b :: T' a -> U') 
                   | si (a :: U') (b :: T' a -> U') 

    T' :: U' -> Set
       = \(x::U')-> case x of 
                      (u) -> U
                      (t a) -> T a
                      (pi a b) -> Pi (T' a) (\(x::T' a) -> T' (b x))
                      (si a b) -> Si (T' a) (\(x::T' a) -> T' (b x))
           
  NextU :: Fam Set
    = struct 
        I = U'
        f = T'

  {- Internal package concerned with predicates over
     a set, where predicates are wrt U T -} 
  package P (D :: Set) where
    Pred :: Set 
      = D -> U 

    Op :: Set
      = D -> D

    Op2 :: Set = D -> Op 

    Contains (P :: Pred) (i :: D) :: Set
      = T (P i) 

    Subset (P :: Pred) (Q :: Pred) :: Set
      = (i :: D)-> 
        P `Contains` i -> Q `Contains` i

    Sub (P :: Pred) (f :: Op) :: Pred 
      = \(i :: D) -> P (f i)

    ClosedUnder (P :: Pred)  (f :: Op) :: Set
      = P `Subset` (P `Sub` f) 

{- To define Gentzen transform need some closure properties
   on U,T. Closure under arrow, and universal 
   quantification over D.  

    Gentzen (P :: Pred) (f :: Op2) :: Pred
      = \(i::D) -> {! P `ClosedUnder` (f i)!}
-}

    PTrans :: Set = Pred -> Pred 

    Monotone (F :: PTrans) :: Set
      = (P,Q :: Pred) -> 
          P `Subset` Q -> F P `Subset` F Q 

    {- The "substitution" predicate transformer
       is monotone. -}

    Observation1 (f :: Op) 
      :: Monotone (\(P :: Pred) -> P `Sub` f)
      = \(P,Q :: Pred) -> 
        \(h :: Subset P Q) -> 
        \(i :: D) -> 
        h (f i) 

    {- Universe with 
        arrow, and quantification over D, -}

    mutual 
      U' :: Set
         = data u 
              | t (a :: U)
              | pid (p :: D -> U') 
              | arr (a :: U') (b :: U') 

      T' :: U' -> Set
         = \(h::U') -> 
           case h of 
               (u) -> U
               (t a) -> T a
               (pid p) -> Pi D (\(i :: D) -> T' (p i))
               (arr a b) -> T' a `arr` T' b

    WeakNext :: Fam Set
      = struct 
          I = U'
          f = T'

package FamP2 (FS :: Fam Set) (D :: Set ) where

  open (FamP FS).P D use WeakNext

  open FamP WeakNext use P, U, T 
  open P D use Pred, Op2, Op

  Subf (P :: Pred) (f :: Op) :: Pred
    = \(h::D) -> P (f h)

  {- We can now define the Gentzen transform -}
  Gentzen' (P :: Pred) (f :: Op2) :: Pred 
    = \(a::D) -> 
      pid@_ (\(b::D) -> arr@_ (P b) (P (f a b)))

  Contains (P :: Pred) (i :: D) :: U
    = P i

  Everywhere (P :: Pred) :: U
    = pid@_ (\(h::D) -> 
        P `Contains` h)

  Subset (P,Q :: Pred) :: U
    = pid@_ (\(h::D) -> 
        arr@_ (P h) (Q h))

  ClosedUnder (P :: Pred) (f :: Op) :: U
    = P `Subset` (P `Subf` f) 
 
  Gentzen (P :: Pred) (f :: Op2) :: Pred 
    = \(a::D) -> 
P `ClosedUnder` (f a) 
