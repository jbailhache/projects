--#include "amenities.agda"
--#include "naturals.agda"

package AEdef  where
  open Amenities use N0, efq, N1, op
  open Naturals  use Nat, NatIt = It

  {- Datatype of notations for gamma_0 -}
  AE :: Set 
    = data O 
         | W (a :: AE) (b :: AE)  
         | V (a :: AE) (b :: AE)

  {- an abbreviation -}
  ItAE :: (f::op AE) -> (n::Nat) -> op AE = NatIt AE

  {- some less barbarous notation, so we can use infix -}
  w (a :: AE) (b :: AE) :: AE = W@_ a b 
  v (a :: AE) (b :: AE) :: AE = V@_ a b 

  {- zero  -} 
  zero :: AE = O@_                   

  {- succ -}
  succ :: op AE = \ (a :: AE) -> a `w` zero

  {- (naught plus) omega-to-the ... -}
  wexp :: op AE = w zero

  {- w with its arguments transposeded. (Convenient.) -}
  wt (a, b :: AE) :: AE = w b a
  
  {- Cofinality of a notation -} 
  C (a :: AE) :: Set
    = case a of 
          (O)     -> N0
          (W _ b) -> case b of 
                      (O)     -> N1
                      (W _ _) -> Nat
                      (V _ _) -> Nat
          (V _ _) -> Nat
  
  {- Immediate predecessors of a notation.
     This enormous definition seems a repellent
     waste of time and paper.  Instead, in the lens
     constructions I have used one or two instances 
     of transfinite recursion to define the veblen hierarchy 
     on a set Ord of `abstract ordinal notations'.
     where O :: Ord, S :: Ord -> Ord, L :: (N -> Ord) -> Ord.
     Exactly why this would not be cheating, I don't know, but
     I'm (almost) sure it is essentially sound. 

     I managed to persuade Anton Setzer, but am not sure what 
     it was I said that convinced him.  When I asked him to 
     persuade me back, he muttered something about the recursion 
    theorem (which one??), and wouldn't elucidate further.
  -}
  pd (x :: AE) (t :: C x) :: AE
    = case x of 
      (O) -> case t of {}
      (W a b) 
          -> case b of 
             (O) -> a 
             (W b1 b2) 
                 -> case b2 of  
                    (O) -> {- a + w^(b1 + 1) -} 
                           ItAE (wt b) t a
                    (W _ _) 
                        -> a `w` pd b t 
                    (V _ _) 
                        -> a `w` pd b t
             (V _ _) -> a `w` pd b t
      (V a b) 
          -> case a of 
             (O) -> {- phi 0 b -} 
                    case b of 
                    (O) -> {- phi 0 0 -} 
                           ItAE wexp t zero
                    (W b1 b2) 
                        -> case b2 of 
                           (O) -> {- phi 0 (b1 + 1) -} 
                                  ItAE wexp t (succ (a `v` b1)) 
                           (W _ _) 
                               -> a `v` pd b t
                           (V _ _) 
                               -> a `v` pd b t
                    (V _ _) -> a `v` (pd b t)
             (W a1 a2) 
                 -> case a2 of
                    (O) -> {- phi (a1 + 1) b -}
                           case b of
                           (O) -> {- phi (a1 + 1) 0 -} 
                                  ItAE (v a) t zero
                           (W b1 b2) 
                               -> case b2 of 
                                  (O) -> {- phi (a1 + 1) (b1 + 1) -} 
                                         ItAE  (v a) t  
                                               (succ (a `v` b1))
                                  (W _ _) 
                                      -> a `v` pd b t 
                                  (V _ _) 
                                      -> a `v` pd b t  
                           (V _ _) 
                               -> a `v` pd b t 
                    (W _ _) 
                        -> case b of 
                           (O) -> {- phi l 0 -} 
                                  pd a t `v` b
                           (W b1 b2) 
                               -> case b2 of 
                                  (O) -> {- phi l (b1 + 1) -} 
                                         pd a t `v` succ (a `v` b1)
                                  (W _ _) 
                                      -> a `v` pd b t
                                  (V _ _) 
                                      -> a `v` pd b t
                           (V _ _) 
                               -> a `v` pd b t
                    (V _ _) 
                        -> case b of 
                           (O) -> pd a t `v` b
                           (W b1 b2) 
                               -> case b2 of 
                                  (O) -> pd a t `v` succ (a `v` b1)
                                  (W _ _) 
                                      -> a `v` pd b t
                                  (V _ _) 
                                      -> a `v` pd b t
                           (V _ _) 
                               -> a `v` pd b t
             (V _ _) 
                 -> case b of 
                    (O) -> pd a t `v` b
                    (W b1 b2) 
                        -> case b2 of 
                           (O) -> {- phi a (b1 + 1) -} 
                                  pd a t `v` succ (a `v` b1)
                           (W _ _) 
                               -> a `v` pd b t
                           (V _ _) 
                               -> a `v` pd b t
                    (V _ _) 
                        -> a `v` pd b t
  Pred :: Type
      = AE -> Set

  {- predicate transformer -}
  PT :: Type
      = Pred -> Pred

  {- PT induced by transition structure -}
  Below :: PT 
      = \(X :: Pred) -> \(a :: AE) ->
        (t :: C a) -> X (pd a t)

  {- Progressivity -}
  Prog (X :: Pred) :: Set
= (a :: AE) -> Below X a -> X a
