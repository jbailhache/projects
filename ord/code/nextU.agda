--#include "amenities.agda"
--#include "naturals.agda"

{- package defining the ordinary kind of `universe over' 
   operator. -}

{- There is a parameter for the type of ordinal terms -}

package UniverseOver (OT :: Set) 
                     ( U :: Set) 
                     ( T :: U -> Set) where 
  open Amenities use N0, N1, Pi, Si
  open Naturals use Nat, NatIt = It, NatItT = ItT

  mutual

    set :: Set 
      = data u | t (x :: U)
           | pi (d :: set) (p :: el d -> set)
           | si (d :: set) (p :: el d -> set)
           | n0code | n1code | natcode
           | otcode

    el :: set -> Set
      =  \ (x :: set) -> 
         case x of 
           (u) -> U
           (t x)    -> T x
           (pi d p) -> Pi (el d) (\(x :: el d) -> el (p x))
           (si d p) -> Si (el d) (\(x :: el d) -> el (p x))
           (n0code)  -> N0
           (n1code)  -> N1
           (natcode) -> Nat
           (otcode)  -> OT

  otcode  :: set = otcode@_
  natcode ::  set = natcode@_
  n0code  :: set = n0code@_
  n1code  :: set = n1code@_
  groundU :: set = u@_
  groundT :: el groundU -> set 
    = \(x :: el groundU) -> t@_ x
  
  pi  (a :: set) (p :: el a -> set) :: set = pi@_ a p 
  si  (a :: set) (p :: el a -> set) :: set = si@_ a p 

  arr (a :: set) (b :: set) :: set = pi a (\(_ :: el a) -> b)  
  and (a :: set) (b :: set) :: set = si a (\(_ :: el a) -> b)  

  op (a :: set ) :: set = a `arr` a

  pin (p :: Nat -> set) :: set = pi natcode (\(n :: Nat) -> p n)
  piot(p :: OT  -> set) :: set = pi otcode  (\(a :: OT ) -> p a)
