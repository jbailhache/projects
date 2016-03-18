{- logical constants, and common amenities -}

package Amenities where

  Fam (A :: Type) :: Type 
    = sig { I :: Set ; i :: I -> A } 

  Fam_map (A, B :: Set) (f :: A -> B)
    :: Fam A -> Fam B
    = \(h::Fam A) -> 
      struct  I = h.I
              i = \(i::I) -> f (h.i i)

  Pow (A :: Type) :: Type 
    = A -> Set

  Pow_map (A, B :: Set) (f :: A -> B)
    :: Pow B -> Pow A
    = \(X :: Pow B) -> 
      \(a :: A) -> 
      X (f a)

  Rel (A, B :: Type) :: Type
    = A -> Pow B

  {--------- functions ----------------------}
  Pi  (A :: Set) (B :: Pow A) :: Set = (a::A) -> B a
  arr (A :: Set) (B :: Set) :: Set
      = Pi A (\(_::A) -> B)
  op  (A :: Set) :: Set = A `arr` A
  op2 (A :: Set) :: Set = A `arr` op A

  implies :: Set -> Set -> Set = arr
  
  {---------- multiplicative things ----------}

  Si  (A :: Set) (B :: Pow A) :: Set 
    = sig fst :: A ; snd :: B fst

  and (A, B :: Set) :: Set
      = Si A (\(_::A) -> B)
  and2 (A :: Set) (B :: Set) (C :: Set) :: Set
      = (A `and` B) `and` C

  andIn (A, B :: Set) :: A -> B -> A `and` B
      = \(a::A) -> \(b::B) ->
        struct  fst = a
                snd = b
  andElimL (A, B :: Set) :: A `and` B -> A
      = \(h::and A B) -> h.fst
  andElimR (A, B :: Set) :: A `and` B -> B
      = \(h::and A B) -> h.snd

  sigIn (A :: Set) (B :: Pow A) 
      :: (a :: A) -> B a -> Si A B 
      = \(a::A) -> \(b::B a) ->
        struct  fst = a
                snd = b

  sigOutL (A :: Set) 
          (B :: Pow A) 
          (h :: Si A B) 
          :: A 
      = h.fst
  sigOutR (A :: Set) 
          (B :: Pow A) 
          (h :: Si A B)
          :: B (sigOutL A B h)
      = h.snd

  split (A :: Set) (B :: Pow A) (C :: Pow (Si A B)) 
        (c :: (a :: A) -> (b :: B a) -> C (sigIn A B a b))
        (h :: Si A B)
        :: C h
      = c (sigOutL A B h) (sigOutR A B h)

  times :: Set -> Set -> Set = and
  pair  :: (A, B :: Set) -> A -> B -> A `and` B
        = andIn
  p0    :: (A, B :: Set) -> A `and` B -> A = andElimL
  p1    :: (A, B :: Set) -> A `and` B -> B = andElimR
  
  {---------- additive things ---------------}
  or (A, B :: Set) :: Set
      = data inl (a :: A) | inr (b :: B)
  orInL (A, B :: Set) :: A -> A `or` B 
      = \(h::A) -> inl@_ h
  orInR (A :: Set) (B :: Set) :: B -> A `or` B 
      = \(h::B) -> inr@_ h
  orElim (A, B, C :: Set) 
         :: (A -> C) -> (B -> C) -> A `or` B -> C
      = \(ha::A -> C) -> \(hb::B -> C) -> \(h0::or A B) -> 
        case h0 of
          (inl a) -> ha a
          (inr b) -> hb b

  plus  :: Set -> Set -> Set = or
  copair:: (A, B, C :: Set) -> 
           (A -> C) -> (B -> C) -> A `plus` B -> C
        = orElim  
  i0 :: (A, B :: Set) -> A `and` B -> A = andElimL
  i1 :: (A, B :: Set) -> A `and` B -> B = andElimR

  {---------- extremal things ----------------}

  {- empty set, absurdity -}
  N0 :: Set = data 
  falsum :: Set = N0
  {- ex falso quodlibet -}                        
  efq (X :: Set) (x :: N0) :: X = case x of {} 

  {- singleton set, vacuity  -}
  N1   :: Set = data n0
  verum  :: Set = N1
  star :: N1 = n0@_
