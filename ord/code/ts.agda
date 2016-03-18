--#include"amenities.agda"
--#include"predicates.agda"
open Amenities use Fam, Pow, Pi, Si

package TransitionSystems where

  structure (S :: Set) :: Type
    = S -> Fam S 

  system :: Type 
    = sig State :: Set
          delta :: structure State

  package Components (sy :: system) 
    where 

    S :: Set = sy.State 
    delta :: structure S = sy.delta 

    T :: S -> Set
      = \(s::S) -> (delta s).I

    after (s :: S) :: T s -> S 
      = (delta s).i

  make (S :: Set)
       (T :: Pow S) 
       (a :: (s :: S) -> T s -> S) :: system 
    = struct 
        State = S
        delta = \(s::State) -> 
                struct I = T s
                       i = \(i::I) -> s `a` i


  package PredT (sy :: system)
    where 

    open Components sy 
         use S, T, after

--    open Predicates S use contains, subset
  
    Box (X :: Pow S) :: Pow S 
      = \(s::S) -> Pi (T s) (\(t::T s) -> X (s `after` t))

    Diamond (X :: Pow S) :: Pow S 
      = \(s::S) -> Si (T s) (\(t::T s) -> X (s `after` t))
  
    Acc :: Pow S 
      = \(s :: S)-> 
        data A (h :: Box Acc s)

    AccIn :: (s :: S) -> Box Acc s -> Acc s
      = \(s :: S)-> \(h::Box Acc s) -> A@_ h 

    AccRec( P :: (s :: S) -> Pow (Acc s) )
          ( pP :: (s :: S) -> 
                  (p :: Box Acc s) -> 
                  (_ :: (t::T s) -> P (s `after` t) (p t)) -> 
                     P s (AccIn s p) )
          (s :: S)
          (a :: Acc s)
          :: P s a 
      = case a of 
          (A p) -> pP s p (\(t::T s) -> 
                              AccRec P pP (s `after` t) (p t))
  
    AccIt (P :: Pow S ) 
          ( pP :: (s :: S)-> Box P s -> P s )
          :: (s :: S) -> Acc s -> P s 
      = AccRec (\(s'::S) -> 
                \(_::Acc s') -> 
                P s')  -- predicate
               (\(s'::S) -> 
                \(_::Box Acc s') -> 
pP s') 
