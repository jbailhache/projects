{- [2000-04-07 21:18:43]
   Proof of accessibility of a system of notations
   for epsilon_0 .
-}

{- Datatype of notations for epsilon_0 -}
AE :: Set  = data O | W (a :: AE) (b :: AE)  

{- some less barbarous notation, so we can use infix -}
w (a :: AE) (b :: AE) :: AE = W@_ a b 

{- zero  -} 
zeroAE :: AE = O@_                   
{- succ -}
succAE (a :: AE) :: AE = a `w` zeroAE

{- Some auxiliary data structures -}

{- empty set -}
N0 :: Set = data       
{- ex falso quodlibet -}                        
efq (X :: Set) (x :: N0) :: X = case x of {} 

{- singleton set -}
N1 :: Set = data n0
{- its element -}
star :: N1 = n0@_

{- natural numbers -}
Nat :: Set = data Z | S (p :: Nat)

{- some less barbarous notation -}
zero :: Nat = Z@_
succ (p :: Nat) :: Nat = S@_ p

{- recursion on Nat -}
Rec (X :: Nat -> Set)      -- predicate
    (x :: X zero)          -- basis
    (f :: (n :: Nat)-> X n -> X (succ n))  -- step
    (n :: Nat) :: X n
  = case n of (Z)   -> x
              (S p) -> f p (Rec X x f p)

{- iteration of operations on AE -}
It (f :: AE -> AE) (n :: Nat) (a :: AE) :: AE
  = Rec (\(_::Nat)->AE) a (\(_::Nat)->f) n

{- Cofinality of a notation -} 
C (x :: AE) :: Set
  = case x of (O)     -> N0
              (W _ b) -> case b of 
                          (O)     -> N1
                          (W _ _) -> Nat

{- Immediate predecessors of a notation -}
pd (a :: AE) (t :: C a) :: AE 
  = case a of 
      (O)       -> case t of {}
      (W a1 a2) -> case a2 of 
           (O) -> a1
           (W b1 b2) -> case b2 of 
                 (O) -> It (\(x::AE) -> x `w` b1) t a1 
                 (W _ _) -> a1 `w` (pd a2 t)

Pred :: Type = AE -> Set
PT :: Type   = Pred -> Pred

{- PT induced by transition structure -}
B :: PT = \(X :: Pred) -> \(a :: AE)->
          (t :: C a) -> X (pd a t) 

{- Progressivity of a predicate -}
Prog (X :: Pred) :: Set  = (a :: AE) -> B X a -> X a

{- Accessibility of a notation with respect to 
   a given predicate -}
Acc :: PT = \(X :: Pred) -> \(a :: AE) -> Prog X -> X a

{- Gentzen's PT -}
G :: PT = \(X :: Pred) -> \(b :: AE) -> 
          (a :: AE) -> X a -> X (a `w` b)

{- G preserves progressivity -}
lemma (X :: Pred) :: Prog X -> Prog (G X)
  = \(p :: Prog X) -> 
    \(b :: AE) -> 
    \(h :: B (G X) b) -> 
    \(a :: AE) -> 
    \(xa :: X a) ->
    let  arg :: B X (a `w` b) 
          = case b of 
            (O) -> (\(t::N1) -> xa) 
            (W b1 b2) -> 
             case b2 of 
               (O)  -> let f :: AE -> AE 
                             = \(x :: AE) -> x `w` b1 
                           itf (n :: Nat) :: AE 
                             = It f n a 
                       in Rec (\(n::Nat) -> X (itf n)) 
                              xa  (\(n::Nat) -> h star (itf n))
               (W _ _) -> (\(t::Nat) -> h t a xa)
    in p (a `w` b) arg

{- All notations are accessible -}
{- RECURSIVE over AE, with a large predicate -}
theorem (a :: AE) (X :: Pred) :: Acc X a
  = \(pX :: Prog X) -> 
    case a of 
      (O)       -> pX zeroAE (\(t::N0)->efq (X (pd zeroAE t)) t)
      (W a' b') -> theorem b' (G X) 
(lemma X pX) a' (theorem a' X pX)
