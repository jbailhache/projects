--#include "amenities.agda"
--#include "naturals.agda"

open Amenities 
     use N0, Si

open Naturals  
     use Nat

{- Successor operation on sets -}
S (A :: Set) :: Set
             = data zero 
                  | succ (a :: A)

{- The least universe containing (A,B) as an 
   internal subfamily, which is closed under
   zero, successor, and sigma. 

   This MIGHT be some kind of "step to the next regular".
-} 
package Univ1 (A :: Set) (B :: A -> Set) where

  mutual

    set :: Set
        = data zero 
             | succ (a :: set)
             | sum  (a :: set)
                    (f :: (x :: el a)-> set) 
             | nat
             | pren 
             | pred (a :: A)

    el (x :: set) :: Set
       =  case x of 
             (zero)    -> N0
             (succ a)  -> S (el a)
             (nat)     -> Nat
             (sum a f) -> Si (el a) (\(x::el a) -> el (f x))
             (pren)    -> A
             (pred a)  -> B a

{- The least universe containing (A,B) as an 
   internal subfamily, which is closed under
   zero, successor, sigma, and the step to the next
   regular.

   This is some kind of "step to the next inaccessible".
-} 
package Univ2 (A :: Set) (B :: A -> Set) where

  mutual

    set :: Set
        = data zero 
             | succ (a :: set)
             | nat
             | sum  (a :: set)
                    (f :: (x :: el a)-> set) 
             | reg  (a :: set)
                    (f :: (x :: el a)-> set) 
             | pren
             | pred (a :: A) 

    el (x :: set) :: Set
       =  case x of 
             (zero)    -> N0
             (succ a)  -> S (el a)
             (nat)     -> Nat
             (sum a f) -> Si (el a) (\(x::el a) -> el (f x))
             (reg a f) -> (Univ1 (el a) (\(x::el a) -> el (f x))).set
             (pren)    -> A
             (pred a)  -> B a

{- The least universe containing (A,B) as an 
   internal subfamily, which is closed under
   zero, successor, sigma, the step to the next
   regular, and the step to the next inaccessible.

   This is some kind of "step to the next hyper-inaccessible".
-} 
package Univ3 (A :: Set) (B :: A -> Set) where

  mutual

    set :: Set
        = data zero 
             | succ (a :: set)
             | nat
             | sum  (a :: set)
                    (f :: (x :: el a)-> set) 
             | reg  (a :: set)
                    (f :: (x :: el a)-> set) 
             | inn  (a :: set)
                    (f :: (x :: el a)-> set) 
             | pren
             | pred (a :: A) 

    el (x :: set) :: Set
       =  case x of 
            (zero)    -> N0
            (succ a)  -> S (el a)
            (nat)     -> Nat
            (sum a f) -> Si (el a) (\(x::el a) -> el (f x))
            (reg a f) -> (Univ1 (el a) (\(x::el a) -> el (f x))).set
            (inn a f) -> (Univ2 (el a) (\(x::el a) -> el (f x))).set
            (pren)    -> A
            (pred a)  -> B a

{- .. and so forth and so on.  What is the uniformity here? -}





