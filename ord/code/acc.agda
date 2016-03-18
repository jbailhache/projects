--#include "naturals.agda"
--#include "amenities.agda"
--#include "ts.agda"
open Amenities use Pow, Fam

package acc (S :: Set) (delta :: S -> Fam S) where 

  T :: Pow S 
    = \(s::S) -> (delta s).I

  pd (s :: S) :: T s -> S
    = \(t::T s) -> (delta s).i t

  Box (P :: Pow S) :: Pow S 
    = \(s :: S) -> 
      (t::T s) -> P (s `pd` t)

  Acc (s :: S) :: Set 
    = data A (p :: Box Acc s) 

  AccRec( P :: (s :: S) -> Pow (Acc s) )
        ( pP :: (s :: S) -> 
                (p :: Box Acc s) -> 
                (_ :: (t::T s) -> P (pd s t) (p t)) -> 
                   P s (A@_ p) )
        (s :: S)
        (a :: Acc s)
        :: P s a 
    = case a of 
        (A p) -> pP s p (\(t::T s) -> 
                            AccRec P pP (s `pd` t) (p t))

  AccIt (P :: Pow S ) 
        ( pP :: (s :: S)-> Box P s -> P s )
        :: (s :: S) -> Acc s -> P s 
    = AccRec (\(s'::S) -> 
              \(_::Acc s') -> 
              P s')  -- predicate
             (\(s'::S) -> 
              \(_::Box Acc s') -> 
pP s') 
